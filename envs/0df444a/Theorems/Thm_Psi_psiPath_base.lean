-- Prove2me | Theorems.Thm_Psi_psiPath_base
-- name    : Psi.psiPath_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:59:32.063975+00:00
-- url     : https://prove2.me/theorems/41a73a32-61ed-4de2-9834-d0af16a51011
-- title:
--   Psi: psi Path base
-- statement:
--   `Ψ` on a base path `(UD)^l U^{k+1} D^{k+1}` returns `(0^l 1^k, [0])`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L396-L465
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L396-L465

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.psiPath_base (l k : ℕ) :
    psiPath ((List.replicate l [true, false]).flatten
              ++ List.replicate (k + 1) true ++ List.replicate (k + 1) false)
      = (List.replicate l false ++ List.replicate k true, [0]) := by sorry
