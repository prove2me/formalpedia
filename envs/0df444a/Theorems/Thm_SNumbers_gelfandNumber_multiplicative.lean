-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_multiplicative
-- name    : SNumbers.gelfandNumber_multiplicative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:24:58.659575+00:00
-- url     : https://prove2.me/theorems/d40f3d13-4dba-423a-b28f-3f49f4422967
-- title:
--   SNumbers: gelfand Number multiplicative
-- statement:
--   **Multiplicativity of the Gelfand numbers**: for `T : X → Y` and `S : Y → Z`,
--   `c_{n+m}(S ∘ T) ≤ cₙ(S) · c_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L345-L388
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L345-L388

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.gelfandNumber_multiplicative (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y) (n m : ℕ) :
    gelfandNumber (S.comp T) (n + m) ≤ gelfandNumber S n * gelfandNumber T m := by sorry
