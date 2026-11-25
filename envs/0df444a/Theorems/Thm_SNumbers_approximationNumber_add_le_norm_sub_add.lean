-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_add_le_norm_sub_add
-- name    : SNumbers.approximationNumber_add_le_norm_sub_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:19.043861+00:00
-- url     : https://prove2.me/theorems/889992b3-3a7a-4917-86bd-9b1929e84e6d
-- title:
--   SNumbers: approximation Number add le norm sub add
-- statement:
--   One pair of approximants for additivity: if `rank L ≤ n` and `rank K ≤ m`, then
--   `a_{n+m}(S + T) ≤ ‖S - L‖ + ‖T - K‖`, witnessed by the approximant `L + K`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L173-L183
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L173-L183

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

theorem SNumbers.approximationNumber_add_le_norm_sub_add {S T L K : X →L[𝕜] Y} {n m : ℕ}
    (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S + T) (n + m) ≤ ‖S - L‖ + ‖T - K‖ := by sorry
