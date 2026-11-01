-- Prove2me | Theorems.Thm_PriceDelegation_lemma_8
-- name    : PriceDelegation.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:43.188276+00:00
-- url     : https://prove2.me/theorems/1eddbf4b-fc23-4ea8-9add-1a14cec1f306
-- title:
--   Lemma 8 — the payment of the contracts of Lemma 7 tends to the learning cost (corrected: the limit is $C(\pi)$, not $\psi$)
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, let $1\le K\le N$, $\rho=K/N$, and let $\lambda^{p-l}$ be the zero of $\Delta$ and $\varphi^{p-l}=\varphi^*(\lambda^{p-l})$. For each large $M$ let $\mu(M)$ be a threshold for which $t^M_{\lambda,\mu(M)}$ solves the problem of Lemma 6.
--
--   1. For the full-learning multiplier $\lambda=\lambda^{f-l}$ and every full-learning policy $\pi^{f-l}$:
--   $$\lim_{M\to\infty}P\big(\pi^{f-l},\{t^M_{\lambda^{f-l},\mu(M)}\}\big)=N\psi=C(\pi^{f-l}).$$
--   2. In the partial-learning regime $\bar F(\varphi^{p-l})\le\rho\le\bar F(\lambda^{p-l})$, with $\eta$ as in Proposition 4 and $\lambda=\lambda^{p-l}$:
--   $$\lim_{M\to\infty}P\big(\pi^{p-l},\{t^M_{\lambda^{p-l},\mu(M)}\}\big)=N\eta\psi=C(\pi^{p-l}).$$
--
--   Since (participation-multi) forces $P\ge C$, the rent of the implementing contract vanishes as $M\to\infty$, which yields the $\varepsilon$-optimality of Corollary 5.
--
--   Differences from the source:
--   - correction: both limits equal $\psi$ → the limits are $N\psi$ and $N\eta\psi$, the learning costs; reason: $P$ sums over $N$ customers; counterexample: Exp(1), $\psi=1/10$, $N=K=2$: $\rho=1\ge\bar F(\lambda^{p-l})$, Lemma 7's pair satisfies (participation-multi), so $P\ge C=2\psi>\psi$ for every $M$; p.23 also substitutes $E[T]$ by $C(\pi)$
--   - reading: $\mu^{f-l}$, $\mu^{p-l}$ of Lemma 7 as functions of $M$ → any choice $\mu(M)$ for which $t^M_{\lambda,\mu(M)}$ solves the problem of Lemma 6 for all large $M$; reason: the other root of the indifference equation keeps a rent and has no vanishing limit
--   - reading: (10): $t^M_{\lambda,\mu}(p)=0$ for $p<\lambda$ and $M\bar F(\mu)/\bar F(p)$ for $\lambda\le p\le\mu$ (p.29) → $t^M_{\lambda,\mu}(p)=0$ for $p\le\lambda$, in particular $t(0)=0$; reason: (reservation) requires $t(p)=0$ for $p\le\lambda$ and the proof of Lemma 6 (p.ec10) writes "0, if $p\le\lambda$"; $t(0)=0$ is the paper's convention (pp.13, 28)
--   - encoding: (IC): $E[t(V)-\psi]\ge\max_{\varphi>0}\{t(\varphi)\bar F(\varphi)+t(0)F(\varphi)\}$ (p.10) → the bound at every $\varphi>0$; reason: a competitor contract need not attain the maximum; the bound at every point is the supremum
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Lemma 8, p.31; proof omitted, p.ec13

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Lemma 8, corrected (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055
(version of Sept. 22, 2021), p.31): as `M → ∞`, the expected payment of the contracts of Lemma 7
tends to the learning cost `C(π)` of the implemented policy: `P(π^{f-l}, T^{f-l}) → N ψ` and
`P(π^{p-l}, T^{p-l}) → N η ψ`. Here `µ(M)` is any choice of threshold for which `t^M_{λ,µ(M)}` solves
the problem of Lemma 6 for all large `M`.

**Corrected**: the page prints the limit `ψ`; `P` sums over `N` customers and is at least `C(π)`
under (participation-multi). -/
theorem lemma_8 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V)
    {lp φp : ℝ} (hlp : 0 ≤ lp) (hΔ : Delta V ψ N lp = 0) (hφp : IsUninf V lp φp) :
    (∀ lf : ℝ, 0 ≤ lf → IsMinOn (Fl V ψ N K) (Ici 0) lf →
      ∀ μ : ℝ → ℝ, (∀ᶠ M in atTop, lf ≤ μ M ∧ SolvesRes V ψ M lf (tRes V M lf (μ M))) →
      ∀ π : Policy N, InPi π → (∀ i, π.q i = 1 ∧ π.θ i = reserve lf) →
        Tendsto (fun M => pay V π (tRes V M lf (μ M))) atTop (𝓝 ((N : ℝ) * ψ))) ∧
    (Fbar V φp ≤ ratio N K → ratio N K ≤ Fbar V lp →
      ∀ η : ℝ, η ∈ Icc (0 : ℝ) 1 → η * Fbar V lp + (1 - η) * Fbar V φp = ratio N K →
      ∀ μ : ℝ → ℝ, (∀ᶠ M in atTop, lp ≤ μ M ∧ SolvesRes V ψ M lp (tRes V M lp (μ M))) →
      ∀ π : Policy N, InPi π →
        (∀ i, π.q i = η ∧ π.θ i = reserve lp ∧ π.φ i = ENNReal.ofReal φp) →
        Tendsto (fun M => pay V π (tRes V M lp (μ M))) atTop (𝓝 ((N : ℝ) * η * ψ))) := by sorry

end PriceDelegation
