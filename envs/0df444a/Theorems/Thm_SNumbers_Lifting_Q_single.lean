-- Prove2me | Theorems.Thm_SNumbers_Lifting_Q_single
-- name    : SNumbers.Lifting.Q_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:39:09.021845+00:00
-- url     : https://prove2.me/theorems/b5ca9a3a-03ff-5b2d-b5b0-58aeb4a80c81
-- title:
--   Lifting: Q single
-- statement:
--   The basis-vector identity: `Q (lp.single 1 ⟨x,h⟩ c) = c • x`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L174-L180
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L174-L180

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

theorem SNumbers.Lifting.Q_single (x : X) (hx : ‖x‖ ≤ 1) (c : 𝕜) :
    letI : DecidableEq (Ball X) := Classical.decEq _
    (Q : BallLp 𝕜 X →L[𝕜] X) (lp.single 1 (⟨x, hx⟩ : Ball X) c) = c • x := by sorry
