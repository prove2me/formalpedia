-- Prove2me | Theorems.Thm_Psi_len_filter_split
-- name    : Psi.len_filter_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:54:22.896052+00:00
-- url     : https://prove2.me/theorems/3b5843f2-cfe8-42bd-b90d-d69a49e7247d
-- title:
--   Psi: len filter split
-- statement:
--   `#0(w) + #1(w) = |w|`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L28-L32
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L28-L32

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.len_filter_split (w : List Bool) :
    (w.filter (· = false)).length + (w.filter id).length = w.length := by sorry
