-- Prove2me | Theorems.Thm_Psi_areaAux_eq_areaH
-- name    : Psi.areaAux_eq_areaH
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:33.546706+00:00
-- url     : https://prove2.me/theorems/0c8799c8-1214-47dd-b92c-e2ea040b4ea3
-- title:
--   Psi: area Aux eq area H
-- statement:
--   The Psi construction uses the area Aux eq area H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L63-L84
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L63-L84

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.areaAux_eq_areaH (p : List Bool) (i e : ℕ) (le : Bool)
    (hle : e ≤ i) (hv : validFrom p ((i : Int) - e)) :
    (areaAux p i e le : Int) = areaH p ((i : Int) - e) le := by sorry
