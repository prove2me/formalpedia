-- Prove2me | Theorems.Thm_SNumbers_multiplicative_approxFamily
-- name    : SNumbers.multiplicative_approxFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:04.688304+00:00
-- url     : https://prove2.me/theorems/fdb3b6ce-3c3f-502f-87cd-6a9ee3020d42
-- title:
--   SNumbers: multiplicative approx Family
-- statement:
--   The approximation numbers are multiplicative: `a_{n+m}(S ∘ T) ≤ aₙ(S) · a_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L419-L420
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L419-L420

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
variable [CompleteSpace 𝕜]
omit [CompleteSpace 𝕜]

theorem SNumbers.multiplicative_approxFamily : Multiplicative (𝕜 := 𝕜) approxFamily := by sorry
