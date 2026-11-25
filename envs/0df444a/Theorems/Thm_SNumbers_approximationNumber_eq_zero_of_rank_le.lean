-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le
-- name    : SNumbers.approximationNumber_eq_zero_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:36.852873+00:00
-- url     : https://prove2.me/theorems/a9a760bc-443f-49fe-91f2-8398091588cb
-- title:
--   SNumbers: approximation Number eq zero of rank le
-- statement:
--   (S4) If `rank S ≤ n`, then `a_n S = 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L150-L156
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L150-L156

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.approximationNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    approximationNumber S n = 0 := by sorry
