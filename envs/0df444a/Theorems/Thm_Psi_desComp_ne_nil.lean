-- Prove2me | Theorems.Thm_Psi_desComp_ne_nil
-- name    : Psi.desComp_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:38.808518+00:00
-- url     : https://prove2.me/theorems/7c1dc3a4-6cdf-480a-90c9-0dfe244957b8
-- title:
--   Psi: des Comp ne nil
-- statement:
--   The Psi construction uses the des Comp ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L542-L542
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L542-L542

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desComp_ne_nil (word : List Bool) : desComp word ≠ [] := by sorry
