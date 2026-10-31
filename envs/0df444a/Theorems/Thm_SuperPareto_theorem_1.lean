-- Prove2me | Theorems.Thm_SuperPareto_theorem_1
-- name    : SuperPareto.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:30.085994+00:00
-- url     : https://prove2.me/theorems/b06a2fbd-4ab4-490f-92ca-73c7782dc079
-- title:
--   Theorem 1, pp.5–6 — a weighted average of WNAID super-Pareto losses stochastically dominates one loss
-- statement:
--   Let $X_1,\dots,X_n$ be weakly negatively associated and identically distributed (WNAID) super-Pareto random variables, let $(\theta_1,\dots,\theta_n)\in\Delta_n$ (so $\theta_i\ge0$, $\sum_i\theta_i=1$), and let $X\overset{d}{=}X_1$.
--
--   1. **Stochastic dominance.**
--   $$
--   X\le_{\mathrm{st}}\sum_{i=1}^n\theta_iX_i, \tag{4}
--   $$
--   and the strict dominance $X<_{\mathrm{st}}\sum_{i=1}^n\theta_iX_i$ holds if $\theta_i>0$ for at least two $i$.
--   2. **Triggering events.** If $X$ is regular, then for any events $A_1,\dots,A_n$ whose family is independent of $(X_1,\dots,X_n)$ and any event $A$ independent of $X$ with $P(A)=\sum_{i=1}^n\theta_iP(A_i)$,
--   $$
--   X\mathbb 1_A\le_{\mathrm{st}}\sum_{i=1}^n\theta_iX_i\mathbb 1_{A_i}. \tag{5}
--   $$
--
--   Here $U\le_{\mathrm{st}}V$ means $P(U\le x)\ge P(V\le x)$ for all $x$, and $U<_{\mathrm{st}}V$ means $P(U>x)<P(V>x)$ whenever $P(U>x)\in(0,1)$. For infinite-mean losses of this kind, pooling raises the probability of exceeding every capital level: diversification is penalized, in contrast with the finite-mean case, where (4) forces $X_1=\dots=X_n$ almost surely (Proposition 2).
--
--   **Formalization Note** WNAID is `IsWNA P Xs` together with `P.map (Xs i) = P.map X` for every $i$, which also encodes $X\overset{d}{=}X_1$. The index set is a finite type of any size ($n=1$ allowed, where the strict clause is vacuous), and the probability space need not be atomless. $\le_{\mathrm{st}}$ is the platform definition `StarShapedRisk.LawInvariant.FSD` (`FSD P U V` means $U\le_{\mathrm{st}}V$) and $<_{\mathrm{st}}$ is `StrictStochLE`. In (ii) the family of events is jointly independent of the vector (`IndepFun` of the indicator vector and the vector), $A$ is independent of $X$, and $X\mathbb 1_A$ is `A.indicator X`.
--
--   Differences from the source:
--   - reading: events A₁, …, Aₙ independent of (X₁, …, Xₙ) → the family (𝟙_{A₁}, …, 𝟙_{Aₙ}) jointly independent of the vector (X₁, …, Xₙ); reason: with each Aᵢ only separately independent of the vector, (5) fails (X₁, X₂ iid Pareto(1), θ = (1/2, 1/2): P(sum > 2) = 7/32 < 8/32 = P(X𝟙_A > 2), see MODERATION_NOTES); the proof needs the events B_S independent of the vector
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: X₁, …, Xₙ WNAID (weakly negatively associated and identically distributed) and X =d X₁ → `IsWNA P Xs` and `P.map (Xs i) = P.map X` for every i; reason: identical laws of all Xᵢ together with X =d X₁ is the same as every Xᵢ having the law of X
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Theorem 1, pp.5–6

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_VaR
import Definitions.Def_SuperPareto_IsSuperPareto
import Definitions.Def_SuperPareto_IsRegularSuperPareto
import Definitions.Def_SuperPareto_IsWNA
import Definitions.Def_SuperPareto_StrictStochLE

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Theorem 1 (main result).** Chen, Embrechts, Wang, *An unexpected stochastic dominance*,
arXiv:2208.08471v4, Theorem 1, pp.5–6: suppose that `X₁, …, Xₙ` are WNAID super-Pareto,
`(θ₁, …, θₙ) ∈ Δₙ`, and `X =d X₁`.

(i) `X ≤st ∑ θᵢXᵢ` (4), and `X <st ∑ θᵢXᵢ` if `θᵢ > 0` for at least two `i ∈ [n]`.

(ii) If `X` is regular, then for any events `A₁, …, Aₙ` independent of `(X₁, …, Xₙ)` and event `A`
independent of `X` satisfying `P(A) = ∑ θᵢ P(Aᵢ)`, `X 𝟙_A ≤st ∑ θᵢ Xᵢ 𝟙_{Aᵢ}` (5).

**Formalization Note.** WNAID: `IsWNA P Xs` (Definition 2, with measurable decreasing sets and the
product form of (2)) and identical laws `P.map (Xs i) = P.map X` for all `i` (which also encodes
`X =d X₁`). The index set `[n]` is a `Fintype` `ι`; `n = 1` is allowed (the strict clause is then
vacuous), and the atomless assumption on the probability space is not made. `FSD P U V`
(platform definition `StarShapedRisk.LawInvariant.FSD`) means `U ≤st V`; `StrictStochLE P U V` is
`U <st V` (§2.2, p.5). In (ii) the family `(A₁, …, Aₙ)` is jointly independent of the vector
`(X₁, …, Xₙ)` (`IndepFun` of the indicator vector and the vector); requiring only each `Aᵢ`
separately to be independent of the vector makes the statement false. `A` is independent of `X`
(`IndepFun` of its indicator and `X`). `X 𝟙_A` is `A.indicator X`. -/
theorem theorem_1 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (X : Ω → ℝ) (Xs : ι → Ω → ℝ) (hX : Measurable X) (hXs : ∀ i, Measurable (Xs i))
    (hWNA : IsWNA P Xs) (hSP : ∀ i, IsSuperPareto P (Xs i)) (hID : ∀ i, P.map (Xs i) = P.map X)
    (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι) :
    (StarShapedRisk.LawInvariant.FSD P X (fun ω => ∑ i, θ i * Xs i ω) ∧
      ((∃ i j, i ≠ j ∧ 0 < θ i ∧ 0 < θ j) →
        StrictStochLE P X (fun ω => ∑ i, θ i * Xs i ω))) ∧
    (IsRegularSuperPareto P X →
      ∀ (A : ι → Set Ω) (A₀ : Set Ω), (∀ i, MeasurableSet (A i)) → MeasurableSet A₀ →
        IndepFun (fun ω i => (A i).indicator (fun _ => (1 : ℝ)) ω) (fun ω i => Xs i ω) P →
        IndepFun (A₀.indicator (fun _ => (1 : ℝ))) X P →
        P.real A₀ = ∑ i, θ i * P.real (A i) →
        StarShapedRisk.LawInvariant.FSD P (A₀.indicator X)
          (fun ω => ∑ i, θ i * (A i).indicator (Xs i) ω)) := by sorry

end SuperPareto
