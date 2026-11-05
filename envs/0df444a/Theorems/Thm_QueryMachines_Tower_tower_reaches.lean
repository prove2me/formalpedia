-- Prove2me | Theorems.Thm_QueryMachines_Tower_tower_reaches
-- name    : QueryMachines.Tower.tower_reaches
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:18.717234+00:00
-- url     : https://prove2.me/theorems/f5ab64f0-f049-417d-a5c5-35ef4f576c8a
-- title:
--   Tower: tower reaches
-- statement:
--   The tower has the runs of `selfCall (nest Sol Inn)`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L99-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/TowerRuns.lean#L99-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}

theorem QueryMachines.Tower.tower_reaches {O : Q ⊕ G → Option A} {S : ℕ} {b : A} {s : (selfCall (nest Sol Inn)).σ} {own : ℕ} {L : List (Q ⊕ G)} (h : (selfCall (nest Sol Inn)).Reaches O S b s own L) :
    (tower Sol Inn).Reaches O S b s own L := by sorry
