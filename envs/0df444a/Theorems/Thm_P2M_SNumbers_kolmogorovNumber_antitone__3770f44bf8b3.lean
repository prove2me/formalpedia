-- Prove2me | Theorems.Thm_P2M_SNumbers_kolmogorovNumber_antitone__3770f44bf8b3
-- name    : P2M_SNumbers_kolmogorovNumber_antitone__3770f44bf8b3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:16:03.863887+00:00
-- url     : https://prove2.me/theorems/195f7055-34c9-44b3-8ee6-77c5278edd5c
-- title:
--   P2 M SNumbers kolmogorov Number antitone  3770f44bf8b3: P2 M SNumbers kolmogorov Number antitone  3770f44bf8b3
-- statement:
--   If `n ≤ m`, then `d_m S ≤ d_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L163-L166
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L163-L166

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem P2M_SNumbers_kolmogorovNumber_antitone__3770f44bf8b3 (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovNumber S m ≤ kolmogorovNumber S n := by sorry

alias «SNumbers».«kolmogorovNumber_antitone'» := P2M_SNumbers_kolmogorovNumber_antitone__3770f44bf8b3
