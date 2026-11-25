-- Prove2me | Theorems.Thm_SNumbers_multiplicative_kolmogorovNumber
-- name    : SNumbers.multiplicative_kolmogorovNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:01:11.107922+00:00
-- url     : https://prove2.me/theorems/bd2ecf95-56ee-48f2-930b-49083dd96baa
-- title:
--   SNumbers: multiplicative kolmogorov Number
-- statement:
--   The Kolmogorov numbers are multiplicative: `d_{n+m}(S ∘ T) ≤ dₙ(S) · d_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L583-L585
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L583-L585

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
variable [CompleteSpace 𝕜]
omit [CompleteSpace 𝕜]

theorem SNumbers.multiplicative_kolmogorovNumber :
    Multiplicative (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by sorry
