-- Prove2me | Theorems.Thm_Psi_psi_valid_head
-- name    : Psi.psi_valid_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:31.517253+00:00
-- url     : https://prove2.me/theorems/b76a4932-ee4c-4c2d-8eeb-1578c0c4e1ac
-- title:
--   Psi: psi valid head
-- statement:
--   Well-definedness (`lem:well-defined`): `Ψ` of a nonempty Dyck path is valid
--   data, and the first height coordinate is `numNBeforeDD π`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L343-L373
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L343-L373

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.psi_valid_head (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by sorry
