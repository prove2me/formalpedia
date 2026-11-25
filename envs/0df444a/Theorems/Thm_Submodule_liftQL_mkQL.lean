-- Prove2me | Theorems.Thm_Submodule_liftQL_mkQL
-- name    : Submodule.liftQL_mkQL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:55.029067+00:00
-- url     : https://prove2.me/theorems/0d3b35e2-1b86-40e5-9b5c-5ae6be8a859c
-- title:
--   Submodule: lift QL mk QL
-- statement:
--   Lifting `f` and then precomposing with the quotient projection recovers
--   `f`: `V.liftQL f h (V.mkQL y) = f y`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L84-L88
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/QuotientMapNorms.lean#L84-L88

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

theorem Submodule.liftQL_mkQL (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) (y : Y) :
    V.liftQL f h (V.mkQL y) = f y := by sorry
