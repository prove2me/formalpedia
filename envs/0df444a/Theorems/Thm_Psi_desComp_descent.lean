-- Prove2me | Theorems.Thm_Psi_desComp_descent
-- name    : Psi.desComp_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:54:41.202232+00:00
-- url     : https://prove2.me/theorems/0924d80a-782f-4df9-ac71-5d4e04c2844a
-- title:
--   Psi: des Comp descent
-- statement:
--   Descent recursion: for `w = 0^a 1^b 0 w'` (with `b ≥ 1`),
--   `Des(0w) = (a+1+b) :: Des(0w')`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L469-L488
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L469-L488

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desComp_descent {w : List Bool} (hnd : noDescent w = false) :
    desComp (false :: w)
      = (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))
        :: desComp (false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) := by sorry
