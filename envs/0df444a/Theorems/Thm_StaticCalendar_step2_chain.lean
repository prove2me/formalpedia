-- Prove2me | Theorems.Thm_StaticCalendar_step2_chain
-- name    : StaticCalendar.step2_chain
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:43.191197+00:00
-- url     : https://prove2.me/theorems/395acb38-91da-4267-b217-d515e209b885
-- title:
--   Step 2 chain, pp.ec13–ec14 (corrected: factor $T$ restored)
-- statement:
--   Let $1\le b_i\le T$, let $x$ be feasible for CDLP-S, and let $b_0\in[1,\min_ib_i]$. With $\rho_i$ the expected per-period demand of item $i$,
--
--   $$
--   \sum_{i=1}^n\mathbb E[\min\{\mathrm{Bin}(T,\rho_i),b_i\}]\cdot p_{\mathsf C,i}\ \ge\ \frac{\mathbb E[\min\{\mathrm{Bin}(T,b_0/T),b_0\}]}{b_0}\cdot T\sum_{S\in\mathcal S}x(S)\sum_{(i,j)\in S}p_jq(i,j,S).
--   $$
--
--   The right side is $\Delta^{APX}(T,b_0)$ times the LP objective at $x$. This is the deterministic last step of the proof of (9).
--
--   Differences from the source:
--   - correction: $\sum_i\mathbb E[\min\{\mathrm{Bin}(T,\rho_i),b_i\}]p_{\mathsf C,i}=\sum_i\frac{\mathbb E[\min\{\mathrm{Bin}(T,\rho_i),b_i\}]}{T\rho_i}\sum_S x(S)\sum_j p_jq(i,j,S)$ and a final line without $T$ → the factor $T$ restored, so the bound is $\Delta^{APX}$ times objective (5); reason: $p_{\mathsf C,i}$ has denominator $\rho_i$, not $T\rho_i$, and (5) carries $T$: with one item, $x=1$, $q=\rho>0$, $p=1$, the left side is $\mathbb E[\min\{\mathrm{Bin}(T,\rho),b\}]$ and the printed middle term is that divided by $T$; every line is short by the same factor, so (9) is unaffected
--   - generalization: $x^*$ an optimal solution of CDLP-S → any feasible $x$; reason: feasibility, constraints (6)–(8), is all the argument uses; an optimal solution is feasible
--   - generalization: $\underline b=\min_ib_i$ → any $b_0\in[1,\min_ib_i]$; reason: $b_0=\min_ib_i$ is the source, and that value is $\ge1$
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Step 2, pp.ec13–ec14

import Mathlib
import Definitions.Def_StaticCalendar_deltaAPX
import Definitions.Def_StaticCalendar_IsLPFeasible
import Definitions.Def_StaticCalendar_lpObjective
import Definitions.Def_StaticCalendar_pC

open MeasureTheory

namespace StaticCalendar

/-- The chain closing Step 2, arXiv:1811.01077v5, pp.ec13–ec14, with the factor `T` restored:
`Σᵢ p_{C,i} E[min{Bin(T,ρᵢ),bᵢ}] ≥ (E[min{Bin(T,b̲/T),b̲}]/b̲) · T Σᵢ Σ_S x(S) Σ_j p_j q(i,j,S)`.

**Formalization Note.** The printed lines each lack a factor `T`: since `p_{C,i}` has denominator
`ρᵢ`, not `Tρᵢ`, the first printed equality is short by `T`, and objective (5) carries `T`. The
right side here is `deltaAPX T b₀ * lpObjective I T x`. -/
theorem step2_chain {n m T : ℕ} (I : DemandModel n m) (b : Fin n → ℝ)
    (hb1 : ∀ i, 1 ≤ b i) (hbT : ∀ i, b i ≤ T) (x : Assortment n m → ℝ)
    (hx : IsLPFeasible I T b x) (b₀ : ℝ) (hb₀ : 1 ≤ b₀) (hb₀b : ∀ i, b₀ ≤ b i) :
    deltaAPX T b₀ * lpObjective I T x ≤ ∑ i, pC I x i * binomMinExp T (rho I x i) (b i) := by sorry

end StaticCalendar
