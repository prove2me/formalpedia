-- Prove2me | Theorems.Thm_SNumbers_half_le_entropyNumber_id_of_lt_rank
-- name    : SNumbers.half_le_entropyNumber_id_of_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:22:41.754298+00:00
-- url     : https://prove2.me/theorems/6e005e29-9bef-5154-aa93-c941d26c9007
-- title:
--   SNumbers: half le entropy Number id of lt rank
-- statement:
--   **`eₙ(id_X) ≥ 1/2` whenever `dim X > n`**: the volume comparison
--   `half_le_entropyNumber_id` in finite dimension, Riesz's lemma otherwise. A single
--   argument through an `(n+1)`-dimensional subspace would need Brunn's section theorem (the
--   covering balls have centres outside the subspace), which Mathlib lacks.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L901-L907
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L901-L907

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

theorem SNumbers.half_le_entropyNumber_id_of_lt_rank (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {n : ℕ} (hn : (n : Cardinal) < Module.rank 𝕜 X) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by sorry
