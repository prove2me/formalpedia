-- Prove2me | Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_antitone
-- name    : SNumbers.Lifting.kolmogorovNumber_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:11:40.260431+00:00
-- url     : https://prove2.me/theorems/4faad2c5-baa4-48ba-a1d1-c87c50257f47
-- title:
--   Lifting: kolmogorov Number antitone
-- statement:
--   The Lifting construction uses the kolmogorov Number antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L196-L198
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean#L196-L198

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_kolmogorovNumber_antitone

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

theorem SNumbers.Lifting.kolmogorovNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (n + 1) ≤ kolmogorovNumber S n := by sorry
