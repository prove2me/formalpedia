-- Prove2me | Theorems.Thm_QuadPTFLearn_fact_8_5
-- name    : QuadPTFLearn.fact_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:46.00381+00:00
-- url     : https://prove2.me/theorems/daf6a5af-e3c1-410a-aa42-720c438a28c1
-- title:
--   Fact 8.5, p.78 — projected stochastic subgradient descent: $\mathbb E[F(\hat w)]\le\min_C F+3RM/(2\sqrt T)$
-- statement:
--   **Projected stochastic subgradient descent** ([Duc18], Corollary 3.4.9). Let $C\subseteq\mathbb R^N$ be a nonempty compact convex set of diameter at most $R>0$ and $F:C\to\mathbb R$ continuous and convex. Suppose a stochastic oracle, using fresh independent randomness on each call, satisfies
--   $$\mathbb E_\xi[G(w,\xi)]\in\partial F(w),\qquad \mathbb E_\xi\big[\|G(w,\xi)\|_2^2\big]\le M^2$$
--   for every $w\in C$, where $M>0$. Then projected stochastic subgradient descent with step sizes $\alpha_t=R/(M\sqrt t)$ and iterate averaging returns $\hat w\in C$ after $T\ge1$ oracle calls such that
--   $$\mathbb E[F(\hat w)]\le\min_{w\in C}F(w)+\frac{3RM}{2\sqrt T}.$$
--
--   This is the optimization step of the hinge-loss learner of Theorem 8.1.
--
--   Differences from the source:
--   - reading: with efficiently computable Euclidean projections → not a hypothesis; reason: a remark on the cost of each step; the guarantee does not use it
--   - reading: iterate averaging, starting point unspecified → ŵ = (1/T) Σ_{t=1}^{T} w_t, the mean of the T points at which the oracle is queried, from any w₁ ∈ C; reason: [Duc18]'s convention
--   - encoding: min_{w∈C} F(w) → the bound against every u ∈ C; reason: the minimum is attained on the compact C
--   - encoding: a stochastic oracle with fresh independent randomness; E_ξ[G] ∈ ∂F(w); E∥G∥² ≤ M²; projection → a jointly measurable G with ξ₀, ξ₁, … i.i.d. from a probability law ν; G(w,·) integrable with F(w) + ⟪E G(w,·), u − w⟫ ≤ F(u) for u ∈ C; ∫⁻ ‖G‖² dν ≤ M²; any nearest-point map onto C; reason: the same oracle; ∂F is the subdifferential relative to C, and the nearest point of a closed convex set is unique
--   - encoding: diameter at most R → dist(x, y) ≤ R for x, y ∈ C; reason: the definition of the diameter
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Fact 8.5 (Projected stochastic subgradient descent; [Duc18], Corollary 3.4.9), p.78 (PDF p.80)

import Mathlib
import Definitions.Def_QuadPTFLearn_PSGD

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Fact 8.5 (Projected stochastic subgradient descent; [Duc18], Corollary 3.4.9), p.78
(PDF p.80).

Let `C ⊆ ℝᴺ` be a nonempty compact convex set of diameter at most `R > 0` and `F : C → ℝ`
continuous and convex. Suppose a stochastic oracle with fresh independent randomness on each
call satisfies `E_ξ[G(w, ξ)] ∈ ∂F(w)` and `E_ξ[‖G(w, ξ)‖₂²] ≤ M²` for every `w ∈ C`, `M > 0`.
Then projected stochastic subgradient descent with step sizes `α_t = R/(M√t)` and iterate
averaging returns `ŵ ∈ C` after `T ≥ 1` oracle calls with
`E[F(ŵ)] ≤ min_{w∈C} F(w) + 3RM/(2√T)`.

**Formalization Note.** "With efficiently computable Euclidean projections" is a remark on cost
and is not a hypothesis. `∂F(w)` is the subdifferential relative to `C`. The oracle is a
jointly measurable `G` with randomness law `ν`, and `ξ₀, ξ₁, …` are i.i.d. `ν`. The bound is
stated against every `u ∈ C`, which is the bound against the minimum (attained on the compact
`C`). The start `w₁ ∈ C` is arbitrary. -/
theorem fact_8_5 {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N))) (hne : K.Nonempty)
    (hcpt : IsCompact K) (hcvx : Convex ℝ K) (R : ℝ) (hR : 0 < R)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R)
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (hFc : ContinuousOn F K) (hFcvx : ConvexOn ℝ K F)
    {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (G : EuclideanSpace ℝ (Fin N) → Ξ → EuclideanSpace ℝ (Fin N))
    (hGm : Measurable (Function.uncurry G)) (M : ℝ) (hM : 0 < M)
    (hG : ∀ w ∈ K, MeasureTheory.Integrable (G w) ν ∧
      (∀ u ∈ K, F w + ⟪∫ ξ, G w ξ ∂ν, u - w⟫ ≤ F u) ∧
      ∫⁻ ξ, ‖G w ξ‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (M ^ 2))
    (proj : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hproj : ∀ y, proj y ∈ K ∧ ∀ c ∈ K, ‖y - proj y‖ ≤ ‖y - c‖)
    (w₁ : EuclideanSpace ℝ (Fin N)) (hw₁ : w₁ ∈ K) (T : ℕ) (hT : 1 ≤ T) :
    (∀ ξ : ℕ → Ξ, psgdAvg proj G R M w₁ T ξ ∈ K) ∧
    ∀ u ∈ K, ∫ ξ, F (psgdAvg proj G R M w₁ T ξ) ∂Measure.infinitePi (fun _ : ℕ => ν) ≤
      F u + 3 * R * M / (2 * Real.sqrt T) := by sorry

end QuadPTFLearn
