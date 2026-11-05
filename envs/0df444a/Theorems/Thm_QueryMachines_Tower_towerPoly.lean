-- Prove2me | Theorems.Thm_QueryMachines_Tower_towerPoly
-- name    : QueryMachines.Tower.towerPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:02:49.149183+00:00
-- url     : https://prove2.me/theorems/6ec6b7a9-512b-4b63-817d-e8abfbd6cded
-- title:
--   Tower: tower Poly
-- statement:
--   The tower has polynomial-time steps, once and for all depths, if the solver and the procedure
--   have.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/PolyTower.lean#L102-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/PolyTower.lean#L102-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Poly
import Definitions.Def_Tower_PolyTower
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork Groundwork.PolyT QueryMachines.QueryMachine
variable {Ctx Q G A : Type} [HasSize Ctx] [Enc Ctx] [Enc Q] [Enc G] [Enc A]
variable (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A) [IsPolyQ Sol] [IsPolyQ Inn]
variable [Carried Ctx]

theorem QueryMachines.Tower.towerPoly : TowerPoly := by sorry
