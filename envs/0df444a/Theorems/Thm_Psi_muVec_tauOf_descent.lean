-- Prove2me | Theorems.Thm_Psi_muVec_tauOf_descent
-- name    : Psi.muVec_tauOf_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:37.227848+00:00
-- url     : https://prove2.me/theorems/da187be9-f6a9-42cd-b360-a58cac8d7689
-- title:
--   Psi: mu Vec tau Of descent
-- statement:
--   The Psi construction uses the mu Vec tau Of descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L81-L91
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L81-L91

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.muVec_tauOf_descent {w : List Bool} (hnd : noDescent w = false) (ha : ℕ)
    (av' : List ℕ) :
    muVec (tauOf w (ha :: av'))
      = ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: muVecAux (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av') ha := by sorry
