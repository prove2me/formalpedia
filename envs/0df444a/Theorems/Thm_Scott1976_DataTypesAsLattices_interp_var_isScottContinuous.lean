-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_interp_var_isScottContinuous
-- name    : Scott1976.DataTypesAsLattices.interp_var_isScottContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:35.088153+00:00
-- url     : https://prove2.me/theorems/e7a404c1-723d-5972-a6bd-d00138a06c6a
-- title:
--   Data Types As Lattices: interp var is Scott Continuous
-- statement:
--   Appendix lemma for Theorem 2.1: abstraction preserves continuity in the other variables.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L249-L351
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L249-L351

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.interp_var_isScottContinuous (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by sorry
