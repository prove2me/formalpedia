-- Prove2me | Theorems.Thm_Psi_isValid_av_cons
-- name    : Psi.isValid_av_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:50.346592+00:00
-- url     : https://prove2.me/theorems/c818d39a-65e0-46c7-871e-2e3f0473483c
-- title:
--   Psi: is Valid av cons
-- statement:
--   `av` is nonempty and its sum splits as head + tail-sum when `w` has a descent.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L624-L629
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L624-L629

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isValid_av_cons (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) : av = av.headD 0 :: av.tail := by sorry
