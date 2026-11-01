-- Prove2me | Theorems.Thm_PriceDelegation_lemma_6
-- name    : PriceDelegation.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:38.717993+00:00
-- url     : https://prove2.me/theorems/6b5da409-f4df-40e4-83d4-15300b163e91
-- title:
--   Lemma 6 — the reservation contract $t^M_{\lambda,\mu}$ solves the bounded single-customer problem with reservation
-- statement:
--   Let $\psi>0$ and let $\lambda\ge0$ be a reservation price. There is $\bar M$ such that for every $M\ge\bar M$ there is a threshold $\mu=\mu(\lambda,M)\ge\lambda$ for which the contract
--   $$
--   t^M_{\lambda,\mu}(p)=\begin{cases}0,&p\le\lambda,\\ \min\{M\bar F(\mu)/\bar F(p),\,M\},&p>\lambda,\end{cases}
--   $$
--   solves
--   $$
--   \max_{t\in\mathcal T}\big\{E[V-t(V)]: t\text{ satisfies (participation), (IC), (limited liability), (M-bounded), (reservation)}\big\},
--   $$
--   where $\mathcal T$ is the set of non-decreasing contracts with $E[t(V)]<\infty$, (participation) is $E[t(V)]\ge\psi$, (IC) is $E[t(V)]-\psi\ge t(\varphi)\bar F(\varphi)+t(0)F(\varphi)$ for every $\varphi>0$, (limited liability) is $t\ge0$, (M-bounded) is $t\le M$ and (reservation) is $t(p)=0$ for $p\le\lambda$.
--
--   Lemma 6 supplies the single-customer building block of the separable contracts of Lemma 7.
--
--   Differences from the source:
--   - reading: (10): $t^M_{\lambda,\mu}(p)=0$ for $p<\lambda$ and $M\bar F(\mu)/\bar F(p)$ for $\lambda\le p\le\mu$ (p.29) → $t^M_{\lambda,\mu}(p)=0$ for $p\le\lambda$, in particular $t(0)=0$; reason: (reservation) requires $t(p)=0$ for $p\le\lambda$ and the proof of Lemma 6 (p.ec10) writes "0, if $p\le\lambda$"; $t(0)=0$ is the paper's convention (pp.13, 28)
--   - encoding: (IC): $E[t(V)-\psi]\ge\max_{\varphi>0}\{t(\varphi)\bar F(\varphi)+t(0)F(\varphi)\}$ (p.10) → the bound at every $\varphi>0$; reason: a competitor contract need not attain the maximum; the bound at every point is the supremum
--   - generalization: a reservation price $\lambda>0$ (p.29) → any $\lambda\ge0$; reason: the multiplier $\lambda^*$ the contract uses can be $0$ (for $K=N$, $\lambda^{f-l}=0$); every $\lambda>0$ is included
--   - generalization: the standing Assumptions 1 and 2 of the paper → not assumed; reason: the statement holds without them; the paper's case is the special case where they hold
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Lemma 6, p.29; (10), p.29; proof, pp.ec10–ec11

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Lemma 6 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), p.29). For a reservation price `λ ≥ 0` there is `M̄` such that for every `M ≥ M̄`
there is a threshold `µ = µ(λ, M) ≥ λ` for which `t^M_{λ,µ}` solves
`max_{t∈𝒯} {E[V − t(V)] : t satisfies (participation), (IC), (limited liability), (M-bounded),
(reservation)}`. -/
theorem lemma_6 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ Mbar : ℝ, ∀ M : ℝ, Mbar ≤ M →
      ∃ μ : ℝ, lam ≤ μ ∧ SolvesRes V ψ M lam (tRes V M lam μ) := by sorry

end PriceDelegation
