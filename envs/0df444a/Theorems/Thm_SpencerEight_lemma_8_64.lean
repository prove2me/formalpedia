-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_64
-- name    : SpencerEight.lemma_8_64
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:03.877093+00:00
-- url     : https://prove2.me/theorems/d4260fcb-a529-401a-8712-34944babcdca
-- title:
--   Lemma 8.64 — a unit logarithmic charge at the mean
-- statement:
--   Let $\mu$ have a log-concave probability density on a finite-dimensional Euclidean space, and let $F$ be a nonnegative lower-semicontinuous convex function with finite mean; $F$ may take the value $+\infty$ on a $\mu$-null set. If $a\ge\mathbb E_\mu[F]$, then
--   $$\mu[F\le a]\ge e^{-1}.$$
--   If $a=0$, this probability is one.
--
--   The lemma replaces the Markov charge for moment bodies by a charge of one unit.
--
--   **Formalization Note** The density is measurable and satisfies `ConvexOptimization.LogConcaveOn` on the whole space (the reused platform definition, with no further condition at $s$ the whole space).
--
--   Differences from the source:
--   - encoding: F nonnegative, possibly +∞, with finite mean; a ≥ E_µ[F] → F valued in ℝ≥0∞, the mean a lintegral, a : ℝ≥0∞ with a ≠ ⊤; reason: the value +∞ is representable, and nonnegativity of the mean gives a ≥ 0
--   - encoding: F convex → the convexity inequality written out in ℝ≥0∞; reason: ℝ≥0∞ is not a real vector space; Lean's 0 · ⊤ = 0 gives the usual extended-value convention
--   - encoding: µ has a log-concave probability density → µ is the volume with density ρ, with ρ measurable, log-concave and of total integral 1; reason: the definition of such a µ
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.64, p.127 (PDF p.127)

import Mathlib
import Definitions.Def_LogConcaveOn
open MeasureTheory
open scoped ENNReal

namespace SpencerEight

/-- Lemma 8.64 (A unit logarithmic charge at the mean), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.127 (PDF p.127).

**Formalization Note** `μ` has the log-concave probability density `ρ` on a finite-dimensional Euclidean space `E`. `F` takes values in `[0, ∞]`, so the value `+∞` on a `μ`-null set is allowed and the mean is a `lintegral`. Convexity is written out for `ℝ≥0∞` values, with `0 · ∞ = 0` at the endpoints. -/
theorem lemma_8_64 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ρ : E → ℝ) (hρm : Measurable ρ) (hρ : ConvexOptimization.LogConcaveOn Set.univ ρ)
    (hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1)
    (F : E → ℝ≥0∞) (hFl : LowerSemicontinuous F)
    (hFc : ∀ x y : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      F (t • x + (1 - t) • y) ≤ ENNReal.ofReal t * F x + ENNReal.ofReal (1 - t) * F y)
    (hFm : ∫⁻ x, F x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) ≠ ⊤)
    (a : ℝ≥0∞) (ha : a ≠ ⊤)
    (hmean : ∫⁻ x, F x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) ≤ a) :
    ENNReal.ofReal (Real.exp (-1)) ≤
        (volume.withDensity fun x => ENNReal.ofReal (ρ x)) {x | F x ≤ a} ∧
    (a = 0 → (volume.withDensity fun x => ENNReal.ofReal (ρ x)) {x | F x ≤ a} = 1) := by sorry

end SpencerEight
