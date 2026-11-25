-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_comp_le_norm_sub_mul
-- name    : SNumbers.approximationNumber_comp_le_norm_sub_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:23.228293+00:00
-- url     : https://prove2.me/theorems/efc46a9c-a677-4bfb-a89f-44cebb5b6948
-- title:
--   SNumbers: approximation Number comp le norm sub mul
-- statement:
--   One pair of approximants for multiplicativity: if `rank L ≤ n` and `rank K ≤ m`, then
--   `a_{n+m}(S ∘ T) ≤ ‖S - L‖ · ‖T - K‖`, witnessed by the approximant
--   `L ∘ T + (S - L) ∘ K`, whose residual is `(S - L) ∘ (T - K)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L203-L226
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L203-L226

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

theorem SNumbers.approximationNumber_comp_le_norm_sub_mul {S L : Y →L[𝕜] Z} {T K : X →L[𝕜] Y}
    {n m : ℕ} (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S.comp T) (n + m) ≤ ‖S - L‖ * ‖T - K‖ := by sorry
