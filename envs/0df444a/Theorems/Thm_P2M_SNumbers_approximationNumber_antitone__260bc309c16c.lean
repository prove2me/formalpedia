-- Prove2me | Theorems.Thm_P2M_SNumbers_approximationNumber_antitone__260bc309c16c
-- name    : P2M_SNumbers_approximationNumber_antitone__260bc309c16c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:20:31.925858+00:00
-- url     : https://prove2.me/theorems/ba2e0a83-c211-48ed-9636-fe9574e80a45
-- title:
--   P2 M SNumbers approximation Number antitone  260bc309c16c: P2 M SNumbers approximation Number antitone  260bc309c16c
-- statement:
--   If `n ≤ m`, then `a_m S ≤ a_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L114-L118
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L114-L118

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

theorem P2M_SNumbers_approximationNumber_antitone__260bc309c16c {S : X →L[𝕜] Y} {n m : ℕ} (h : n ≤ m) :
    approximationNumber S m ≤ approximationNumber S n := by sorry

alias «SNumbers».«approximationNumber_antitone'» := P2M_SNumbers_approximationNumber_antitone__260bc309c16c
