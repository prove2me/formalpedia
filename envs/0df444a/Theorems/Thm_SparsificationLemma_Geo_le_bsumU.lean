-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_le_bsumU
-- name    : SparsificationLemma.Geo.le_bsumU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:25:40.20504+00:00
-- url     : https://prove2.me/theorems/e1c2534b-49af-4ec2-b2eb-75e63337d225
-- title:
--   Geo: le bsum U
-- statement:
--   k ≤ τ^(2k), if 2 ≤ τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Tau.lean#L31-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Tau.lean#L31-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsificationLemma_Geo_Tau
import Theorems.Thm_UniformInK_Leaves_le_bsumU

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK

theorem SparsificationLemma.Geo.le_bsumU {k τ : ℕ} (hτ : 2 ≤ τ) : k ≤ bsumU τ k := by sorry
