-- Prove2me | Theorems.Thm_SupportVectorMachines_Regression_theorem_A_8_1_symmetrization
-- name    : SupportVectorMachines.Regression.theorem_A_8_1_symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:57.606272+00:00
-- url     : https://prove2.me/theorems/7e9690a5-a75e-416a-8053-dc5c3a504db1
-- title:
--   Theorem A.8.1 — the symmetrization inequality
-- statement:
--   This is Theorem A.8.1 (Symmetrization) of Steinwart & Christmann, *Support Vector Machines*
--   (Springer 2008, p. 535, Appendix §A.8), the first of the two general Banach-space
--   probability results this mission's goal (Lemma 9.2) invokes in its own proof ("Using the
--   symmetrization argument given in Theorem A.8.1, we have...").
--
--   Let $\Psi : [0,\infty) \to [0,\infty)$ be convex and non-decreasing, $E$ a separable Banach
--   space, $(\Omega,\mathcal A, P)$ a probability space, $\xi_1,\dots,\xi_n : \Omega \to E$
--   i.i.d. $P$-integrable random variables, and $\varepsilon_1,\dots,\varepsilon_n$ a Rademacher
--   sequence with respect to some distribution $\nu$. Then
--   $$
--   \mathbb E_P\, \Psi\!\left(\left\|\frac1n\sum_{i=1}^n(\xi_i - \mathbb E_P\xi_i)\right\|\right)
--   \le
--   \mathbb E_P\,\mathbb E_\nu\, \Psi\!\left(2\left\|\frac1n\sum_{i=1}^n \varepsilon_i\xi_i\right\|\right).
--   $$
--
--   The inequality is the standard device for replacing a centered i.i.d. sum by a Rademacher-
--   randomized one, at the cost of a factor $2$ inside $\Psi$: it lets the rest of the argument
--   reason about the (often much easier to bound) randomized sum instead of the original
--   dependence structure of $\xi_1,\dots,\xi_n$ on $(\Omega,P)$.
--
--   **Formalization Note** "$E$ a separable Banach space" is `[NormedAddCommGroup E]
--   [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]` (Mathlib's
--   `TopologicalSpace.SeparableSpace`); "i.i.d." is `iIndepFun` (independence) together with
--   `∀ i j, IdentDistrib (ξ i) (ξ j) P P` (pairwise identical distribution, the standard
--   Mathlib rendering of "identically distributed" for a finite family). The book's codomain
--   restriction $\Psi : [0,\infty) \to [0,\infty)$ is rendered as an explicit `hΨnn : ∀ x ∈
--   Set.Ici (0:ℝ), 0 ≤ Ψ x` hypothesis plus `hΨmeas : Measurable Ψ`, and both expectations are
--   `ℝ≥0∞`-valued `lintegral`s (`∫⁻`) composing `Ψ` through `ENNReal.ofReal`, rather than
--   real-valued Bochner integrals — matching exactly why the book restricts $\Psi$'s codomain to
--   $[0,\infty)$ in the first place: it is what lets $\mathbb E_P\Psi(\cdots)$ and $\mathbb
--   E_P\mathbb E_\nu\Psi(\cdots)$ be always-defined, possibly infinite, expectations with no
--   integrability hypothesis on the $\Psi$-composed integrand anywhere in the book's own
--   statement (a Bochner integral would instead silently return $0$ on a non-integrable
--   integrand, and nothing here rules that out: $\Psi$ need only be convex and non-decreasing,
--   hence of arbitrary growth, while $\xi_1,\dots,\xi_n$ are only assumed first-moment
--   integrable). The two innermost $\mathbb E_P\xi_i$ terms remain ordinary Bochner integrals,
--   since $\xi_i$ itself is genuinely assumed $P$-integrable by hypothesis.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 535, Theorem A.8.1

import Mathlib
import Definitions.Def_SupportVectorMachines_Regression_IsRademacherSequence

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace SupportVectorMachines.Regression

/-- Theorem A.8.1 (Symmetrization), p. 535: let `Ψ : [0,∞) → [0,∞)` be convex and non-decreasing,
`E` a separable Banach space, `(Ω,A,P)` a probability space, `ξ₁,…,ξₙ : Ω → E` i.i.d.
`P`-integrable random variables, and `ε₁,…,εₙ` a Rademacher sequence with respect to some `ν`.
Then `E_P Ψ(‖(1/n) ∑ᵢ(ξᵢ - E_P ξᵢ)‖) ≤ E_P E_ν Ψ(2‖(1/n) ∑ᵢ εᵢξᵢ‖)`. The book's `Ψ : [0,∞) → [0,∞)`
codomain restriction (nonnegativity) is what lets both expectations be always-defined, possibly
infinite, quantities with no integrability hypothesis anywhere in the statement; rendered here as
`ℝ≥0∞`-valued `lintegral`s composing `Ψ` through `ENNReal.ofReal`, with an explicit `hΨnn`/`hΨmeas`
in place of the book's `[0,∞) → [0,∞)` codomain, rather than as real-valued Bochner integrals
(which would silently return the junk value `0` on a non-integrable `Ψ`-composed integrand — no
such integrability is assumed or available here, since `Ψ` need only be convex and non-decreasing,
hence of arbitrary growth). -/
theorem theorem_A_8_1_symmetrization
    (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ) (hΨmono : MonotoneOn Ψ (Set.Ici 0))
    (hΨnn : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ Ψ x) (hΨmeas : Measurable Ψ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SeparableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (ξ : Fin n → Ω → E) (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ P) (hξident : ∀ i j, IdentDistrib (ξ i) (ξ j) P P)
    (hξint : ∀ i, Integrable (ξ i) P)
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (ε : Fin n → Θ → ℝ) (hε : IsRademacherSequence ε ν) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ‖(n : ℝ)⁻¹ • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P ≤
      ∫⁻ ω, ∫⁻ θ, ENNReal.ofReal (Ψ (2 * ‖(n : ℝ)⁻¹ • ∑ i, ε i θ • ξ i ω‖)) ∂ν ∂P := by sorry

end SupportVectorMachines.Regression
