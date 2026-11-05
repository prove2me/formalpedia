-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490
-- name    : P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:28.944646+00:00
-- url     : https://prove2.me/theorems/1d2c4de9-7ddf-4bcf-a903-8330afc80e3a
-- title:
--   P2 M Groundwork Grid sum   ix Of e2b52bf0c490: P2 M Groundwork Grid sum   ix Of e2b52bf0c490
-- statement:
--   A sum over the rectangles is the sum over their numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L167-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L167-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)

theorem P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490 (g : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin g) (Fin g), f (ixOf g ω) = ∑ q ∈ range (nRect g), f q := by sorry

alias «Groundwork».«Grid».«sum_Ω_ixOf» := P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490
