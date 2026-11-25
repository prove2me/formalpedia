-- Prove2me | Theorems.Thm_SNumbers_le_entropyNumber_of_separated
-- name    : SNumbers.le_entropyNumber_of_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:42:25.99316+00:00
-- url     : https://prove2.me/theorems/5f8ae78c-c126-4852-9e6c-d74f15bc947c
-- title:
--   SNumbers: le entropy Number of separated
-- statement:
--   **Separation bounds the entropy numbers from below.** If `S(B_X)` contains
--   more than `2 ^ n` points that are pairwise at distance at least `δ`, then
--   `eₙ(S) ≥ δ/2`.
--
--   The boxes of the pigeonhole are the balls of an admissible cover, the objects
--   are the given points. Suppose a radius `ε < δ/2` were admissible. Sending each
--   point to a covering centre is then injective: two points sharing a centre `y`
--   are both within `ε` of `y`, hence within `2ε < δ` of each other, which the
--   separation forbids. So there are at least as many centres as points, i.e.
--   `2 ^ n < P.card ≤ 2 ^ n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L239-L270
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L239-L270

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.le_entropyNumber_of_separated {S : X →L[𝕜] Y} {n : ℕ} {δ : ℝ} {P : Finset Y}
    (hP : ↑P ⊆ ⇑S '' Metric.closedBall 0 1) (hcard : 2 ^ n < P.card)
    (hsep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → δ ≤ dist z z') :
    δ / 2 ≤ entropyNumber S n := by sorry
