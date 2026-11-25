-- Prove2me | Theorems.Thm_Submodule_norm_mkQL_apply_le
-- name    : Submodule.norm_mkQL_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:00.086211+00:00
-- url     : https://prove2.me/theorems/23ef83c3-6e0f-4b45-9dde-1499453794d5
-- title:
--   Submodule: norm mk QL apply le
-- statement:
--   Pointwise form of `norm_mkQL_le`: passing to the quotient does not
--   increase the norm, `‖V.mkQL y‖ ≤ ‖y‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L78-L80
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L78-L80

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

theorem Submodule.norm_mkQL_apply_le (V : Submodule 𝕜 Y) (y : Y) : ‖V.mkQL y‖ ≤ ‖y‖ := by sorry
