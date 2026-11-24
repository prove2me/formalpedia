-- Prove2me | Theorems.Thm_Psi_firstDDidx_key
-- name    : Psi.firstDDidx_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:22.513129+00:00
-- url     : https://prove2.me/theorems/6e3d52d7-6911-4df4-ab65-031414196bc1
-- title:
--   Psi: first DDidx key
-- statement:
--   Case analysis for `firstDDidx` on a two-element-plus prefix.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L77-L91
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L77-L91

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_key (a b : Bool) (u : List Bool) (i : ℕ)
    (h : firstDDidx (a :: b :: u) = some i) :
    (a = false ∧ b = false ∧ i = 0) ∨
      (∃ j, firstDDidx (b :: u) = some j ∧ i = j + 1 ∧ ¬(a = false ∧ b = false)) := by sorry
