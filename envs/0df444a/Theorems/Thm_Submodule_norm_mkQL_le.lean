-- Prove2me | Theorems.Thm_Submodule_norm_mkQL_le
-- name    : Submodule.norm_mkQL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:10:04.087644+00:00
-- url     : https://prove2.me/theorems/3581239f-8111-4118-af0a-ff198047603f
-- title:
--   Submodule: norm mk QL le
-- statement:
--   The quotient projection `V.mkQL : Y →L[𝕜] (Y ⧸ V)` is a contraction.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L71-L74
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L71-L74

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

theorem Submodule.norm_mkQL_le (V : Submodule 𝕜 Y) : ‖V.mkQL‖ ≤ 1 := by sorry
