-- Prove2me | Theorems.Thm_PriceDelegation_lemma_7
-- name    : PriceDelegation.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:41.346896+00:00
-- url     : https://prove2.me/theorems/f121cb1b-9972-4b8f-acc3-d6584cfb3862
-- title:
--   Lemma 7 — the separable contracts $T^{f-l}$, $T^{p-l}$ implement $\pi^{f-l}$, $\pi^{p-l}$
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, let $1\le K\le N$, $\rho=K/N$, and let $\lambda^{p-l}$ be the zero of $\Delta$ and $\varphi^{p-l}=\varphi^*(\lambda^{p-l})$.
--
--   1. Let $\lambda^{f-l}$ minimize $N(E[(V-\lambda)^+]-\psi)+K\lambda$ over $\lambda\ge0$. There is $\bar M$ such that for every $M>\bar M$ there is $\mu^{f-l}\ge\lambda^{f-l}$ for which $t^M_{\lambda^{f-l},\mu^{f-l}}$ solves the problem of Lemma 6 and, with $T^{f-l}=\{t^M_{\lambda^{f-l},\mu^{f-l}}\}$, every full-learning policy $\pi^{f-l}$ ($q_i=1$, reservation price $\lambda^{f-l}$, any $\varphi_i$) satisfies (IC-multi) and (participation-multi).
--   2. Suppose $\bar F(\varphi^{p-l})\le\rho\le\bar F(\lambda^{p-l})$ and $\eta\in[0,1]$ satisfies $\eta\bar F(\lambda^{p-l})+(1-\eta)\bar F(\varphi^{p-l})=\rho$. There is $\bar M$ such that for every $M>\bar M$ there is $\mu^{p-l}\ge\lambda^{p-l}$ for which $t^M_{\lambda^{p-l},\mu^{p-l}}$ solves the problem of Lemma 6 and $(\pi^{p-l},T^{p-l})$ satisfies (IC-multi) and (participation-multi), where $T^{p-l}=\{t^M_{\lambda^{p-l},\mu^{p-l}}\}$.
--
--   (IC-multi) means that the policy is inventory feasible and maximizes the agent's utility $P(\pi,T)-C(\pi)$ over all inventory-feasible policies; (participation-multi) means $P(\pi,T)-C(\pi)\ge0$.
--
--   Differences from the source:
--   - reading: "For every M > M̄", with $\bar M$ not quantified → there exists $\bar M$ (depending on the data); reason: the only reading under which the statement has content
--   - reading: "there exist µf-l and µp-l" → a threshold for which $t^M_{\lambda,\mu}$ solves the problem of Lemma 6; reason: the proof uses (EC.6), which holds for Lemma 6's $\mu(\lambda,M)$; the indifference equation has a second root that leaves a rent
--   - generalization: prices $\theta_i(\cdot)>0$, $\varphi_i>0$ in $\Pi$ (p.21), $\geq0$ in (6) (p.23), with the price $\infty$ allowed (p.9) → every price ranges over $[0,\infty]$; reason: a larger policy set: (IC-multi) quantifies over more deviations and $J^{FB-MC}$ over more policies; the target policies are in both sets, so the statement specializes to the page's
--   - encoding: informed price policies $\theta_i(\cdot)$ (p.21) → $\theta_i$ is measurable; reason: the expectations $E[1\{V\ge\theta_i(V)\}]$ that define $I$, Rev and $P$ exist only for measurable $\theta_i$
--   - reading: (10): $t^M_{\lambda,\mu}(p)=0$ for $p<\lambda$ and $M\bar F(\mu)/\bar F(p)$ for $\lambda\le p\le\mu$ (p.29) → $t^M_{\lambda,\mu}(p)=0$ for $p\le\lambda$, in particular $t(0)=0$; reason: (reservation) requires $t(p)=0$ for $p\le\lambda$ and the proof of Lemma 6 (p.ec10) writes "0, if $p\le\lambda$"; $t(0)=0$ is the paper's convention (pp.13, 28)
--   - encoding: (IC): $E[t(V)-\psi]\ge\max_{\varphi>0}\{t(\varphi)\bar F(\varphi)+t(0)F(\varphi)\}$ (p.10) → the bound at every $\varphi>0$; reason: a competitor contract need not attain the maximum; the bound at every point is the supremum
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Lemma 7, p.30; proof, pp.ec11–ec12

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Lemma 7 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), p.30). Let `λ^{p-l}` be the zero of `∆` and `φ^{p-l} = φ*(λ^{p-l})`.
1. For the full-learning multiplier `λ^{f-l}`, there is `M̄` such that for every `M > M̄` there is
   `µ^{f-l}` for which `t^M_{λ^{f-l},µ^{f-l}}` solves the problem of Lemma 6 and, with
   `T^{f-l} = {t^M_{λ^{f-l},µ^{f-l}}}`, every policy `π^{f-l}` satisfies (IC-multi) and
   (participation-multi).
2. In the partial-learning regime `F̄(φ^{p-l}) ≤ ρ ≤ F̄(λ^{p-l})`, with `η` as in Proposition 4,
   there is `M̄` such that for every `M > M̄` there is `µ^{p-l}` for which `t^M_{λ^{p-l},µ^{p-l}}` solves
   the problem of Lemma 6 and `(π^{p-l}, T^{p-l})` satisfies (IC-multi) and (participation-multi).

**Formalization Note** `µ` is required to solve the problem of Lemma 6: the indifference equation
has two roots, and only this one makes the rent vanish (`lemma_8`). -/
theorem lemma_7 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V)
    {lp φp : ℝ} (hlp : 0 ≤ lp) (hΔ : Delta V ψ N lp = 0) (hφp : IsUninf V lp φp) :
    (∀ lf : ℝ, 0 ≤ lf → IsMinOn (Fl V ψ N K) (Ici 0) lf →
      ∃ Mbar : ℝ, ∀ M : ℝ, Mbar < M → ∃ μ : ℝ, lf ≤ μ ∧ SolvesRes V ψ M lf (tRes V M lf μ) ∧
        ∀ π : Policy N, InPi π → (∀ i, π.q i = 1 ∧ π.θ i = reserve lf) →
          IsBestResponse V ψ K π (tRes V M lf μ) ∧ Participates V ψ π (tRes V M lf μ)) ∧
    (Fbar V φp ≤ ratio N K → ratio N K ≤ Fbar V lp →
      ∀ η : ℝ, η ∈ Icc (0 : ℝ) 1 → η * Fbar V lp + (1 - η) * Fbar V φp = ratio N K →
      ∃ Mbar : ℝ, ∀ M : ℝ, Mbar < M → ∃ μ : ℝ, lp ≤ μ ∧ SolvesRes V ψ M lp (tRes V M lp μ) ∧
        ∀ π : Policy N, InPi π →
          (∀ i, π.q i = η ∧ π.θ i = reserve lp ∧ π.φ i = ENNReal.ofReal φp) →
          IsBestResponse V ψ K π (tRes V M lp μ) ∧ Participates V ψ π (tRes V M lp μ)) := by sorry

end PriceDelegation
