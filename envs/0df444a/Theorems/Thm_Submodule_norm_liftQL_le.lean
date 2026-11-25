-- Prove2me | Theorems.Thm_Submodule_norm_liftQL_le
-- name    : Submodule.norm_liftQL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:10:27.464601+00:00
-- url     : https://prove2.me/theorems/c460540c-76f0-4062-b17e-ab6ab44071ff
-- title:
--   Submodule: norm lift QL le
-- statement:
--   The lift `V.liftQL f h : (Y ⧸ V) →L[𝕜] Z` does not increase the operator
--   norm: `‖V.liftQL f h‖ ≤ ‖f‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L92-L115
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L92-L115

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Definitions.Def_SNumbers_QuotientMapNorms
set_option autoImplicit true
@[expose] public section
public section
open Submodule
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem Submodule.norm_liftQL_le (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) :
    ‖V.liftQL f h‖ ≤ ‖f‖ := by sorry
