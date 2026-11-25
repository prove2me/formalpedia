-- Prove2me | Theorems.Thm_SNumbers_half_le_entropyNumber_id
-- name    : SNumbers.half_le_entropyNumber_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:49:38.292246+00:00
-- url     : https://prove2.me/theorems/04ad5632-034c-4537-a5f2-417960a6874d
-- title:
--   SNumbers: half le entropy Number id
-- statement:
--   **`eₙ(id_X) ≥ 1/2` whenever `dim X > n`.** Scaling a ball by `ε` scales its
--   volume by `ε ^ D`, so a cover of the unit ball by `2 ^ n` balls of radius `ε`
--   gives `1 ≤ 2 ^ n · ε ^ D`; with `ε ≤ 1/2` and `D ≥ n+1` the right-hand side
--   would be at most `1/2`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L776-L838
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L776-L838

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

theorem SNumbers.half_le_entropyNumber_id (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] {n : ℕ}
    (hn : n < Module.finrank 𝕜 X) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by sorry
