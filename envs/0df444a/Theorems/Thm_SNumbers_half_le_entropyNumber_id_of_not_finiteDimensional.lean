-- Prove2me | Theorems.Thm_SNumbers_half_le_entropyNumber_id_of_not_finiteDimensional
-- name    : SNumbers.half_le_entropyNumber_id_of_not_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:05:36.768705+00:00
-- url     : https://prove2.me/theorems/dc6967fb-bed2-5aaa-8be6-e42798a75ac5
-- title:
--   SNumbers: half le entropy Number id of not finite Dimensional
-- statement:
--   **`eₙ(id_X) ≥ 1/2` on infinite-dimensional spaces.** For every `R > 1`, Riesz's lemma
--   gives a sequence in the ball of radius `R` whose points are at mutual distance at least `1`
--   (`exists_seq_norm_le_one_le_norm_sub'`); rescaled by `R⁻¹`, any `2ⁿ + 1` of them lie in
--   `B_X` at mutual distance at least `1/R`, so `eₙ(id_X) ≥ 1/(2R)` by
--   `le_entropyNumber_of_separated`. Letting `R → 1` gives the claim.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L845-L895
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L845-L895

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
open MeasureTheory

theorem SNumbers.half_le_entropyNumber_id_of_not_finiteDimensional (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (hX : ¬FiniteDimensional 𝕜 X) (n : ℕ) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by sorry
