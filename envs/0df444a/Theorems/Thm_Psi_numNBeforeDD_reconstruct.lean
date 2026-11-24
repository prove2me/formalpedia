-- Prove2me | Theorems.Thm_Psi_numNBeforeDD_reconstruct
-- name    : Psi.numNBeforeDD_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:55.947995+00:00
-- url     : https://prove2.me/theorems/64c9b96e-8b7c-4b5e-8880-7789de38a2a5
-- title:
--   Psi: num NBefore DD reconstruct
-- statement:
--   `numNBeforeDD` of the recursive reconstructed path
--   `(UD)^a U ρ U^b D^{b+1} ρ'`: the first `DD` sits in the pyramid `D^{b+1}`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L144-L180
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L144-L180

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.numNBeforeDD_reconstruct (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρDD : hasDD ρ = false) :
    numNBeforeDD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = a + 1 + numN ρ + b := by sorry
