-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_geom_le
-- name    : SparsificationLemma.Cal.geom_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:11:08.672759+00:00
-- url     : https://prove2.me/theorems/decbe6c8-b948-4b68-88a8-b7941302ae35
-- title:
--   Cal: geom le
-- statement:
--   2·(1 + q + … + q^m) ≤ 4·q^m for q ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L93-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L93-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset

theorem SparsificationLemma.Cal.geom_le {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : ∑ i ∈ range (m + 1), 2 * q ^ i ≤ 4 * q ^ m := by sorry
