-- Prove2me | Theorems.Thm_Psi_muVecAux_map_add
-- name    : Psi.muVecAux_map_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:20.748585+00:00
-- url     : https://prove2.me/theorems/411f57bf-57b2-473a-8462-10aa834f05fb
-- title:
--   Psi: mu Vec Aux map add
-- statement:
--   The Psi construction uses the mu Vec Aux map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L31-L37
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L31-L37

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.muVecAux_map_add (M : List ℕ) (q c : ℕ) :
    muVecAux (M.map (· + c)) (q + c) = muVecAux M q := by sorry
