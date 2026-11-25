-- Prove2me | Theorems.Thm_SNumbers_Lifting_norm_Q_le
-- name    : SNumbers.Lifting.norm_Q_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:43:59.884101+00:00
-- url     : https://prove2.me/theorems/8572e1bc-4b16-401f-bfd0-2f05a696c64c
-- title:
--   Lifting: norm Q le
-- statement:
--   The Lifting construction uses the norm Q le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L170-L171
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L170-L171

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]

theorem SNumbers.Lifting.norm_Q_le : ‖(Q : BallLp 𝕜 X →L[𝕜] X)‖ ≤ 1 := by sorry
