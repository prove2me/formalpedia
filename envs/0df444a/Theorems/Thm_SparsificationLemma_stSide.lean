-- Prove2me | Theorems.Thm_SparsificationLemma_stSide
-- name    : SparsificationLemma.stSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:05:28.147207+00:00
-- url     : https://prove2.me/theorems/59b434c0-9da4-4a09-b8bc-52173f80b6d4
-- title:
--   Sparsification Lemma: st Side
-- statement:
--   The tree that starts with the side list X has the same first components, and X behind every side
--   list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L29-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L29-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_SparsifyList
import Definitions.Def_SparsificationLemma_Side
set_option autoImplicit false
section
section
open SparsificationLemma
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate

theorem SparsificationLemma.stSide : StSide := by sorry
