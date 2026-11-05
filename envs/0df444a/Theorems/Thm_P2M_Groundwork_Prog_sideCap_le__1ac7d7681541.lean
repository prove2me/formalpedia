-- Prove2me | Theorems.Thm_P2M_Groundwork_Prog_sideCap_le__1ac7d7681541
-- name    : P2M_Groundwork_Prog_sideCap_le__1ac7d7681541
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:25.875377+00:00
-- url     : https://prove2.me/theorems/7f0e043b-1768-434b-afb9-ccdea60ab848
-- title:
--   P2 M Groundwork Prog side Cap le  1ac7d7681541: P2 M Groundwork Prog side Cap le  1ac7d7681541
-- statement:
--   A bound on the label bits of a pair of parts for every n (`Grid.sideCap_le` of
--   StepMachines/Math/SideNet.lean needs 1 ≤ n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/GridSide.lean#L117-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/GridSide.lean#L117-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Cut
import Definitions.Def_ToTuring_Poly_Grid
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ToTuring_Poly_GridSide
import Theorems.Thm_Groundwork_Grid_rectLen_le
import Theorems.Thm_Groundwork_Grid_sideCnt_rectDig_le

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Stepped
open Groundwork.Grid (sideCnt he node c2 rectIx rectDig rectLen sideChunk sideCap sideCnt_rectDig_le rectLen_le)
variable {α : Type} [Enc α] (g : ℕ) (tr : Bool)

theorem P2M_Groundwork_Prog_sideCap_le__1ac7d7681541 (n y a b : ℕ) : sideCap g tr n y a b ≤ g * n + c2 g * (3 * n + 1) := by sorry

alias «Groundwork».«Prog».«sideCap_le'» := P2M_Groundwork_Prog_sideCap_le__1ac7d7681541
