-- Prove2me | Theorems.Thm_SNumbers_isPseudoSNumberSequence_entropyNumber
-- name    : SNumbers.isPseudoSNumberSequence_entropyNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:23:19.298319+00:00
-- url     : https://prove2.me/theorems/fe672617-95eb-45f2-a89d-f12fd39cec41
-- title:
--   SNumbers: is Pseudo SNumber Sequence entropy Number
-- statement:
--   **The entropy numbers are a pseudo-s-number sequence**: they satisfy (S1)–(S3).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L309-L315
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L309-L315

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

theorem SNumbers.isPseudoSNumberSequence_entropyNumber :
    IsPseudoSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => entropyNumber S n) := by sorry
