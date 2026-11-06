-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_poly_le
-- name    : SparsificationLemma.Mach.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:40.683103+00:00
-- url     : https://prove2.me/theorems/a6e5c256-41d4-4302-a4dc-49ea130a46c8
-- title:
--   Mach: poly le
-- statement:
--   C·(length of the input + 8)^C ≤ c·(n+1)^c with c = C·(s+412)^C + 4C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/LemSparsification.lean#L52-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/LemSparsification.lean#L52-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

theorem SparsificationLemma.Mach.poly_le (C s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    C * ((encIn s 3 φ).length + 2 ^ 3) ^ C ≤ (C * (s + 412) ^ C + 4 * C) * (n + 1) ^ (C * (s + 412) ^ C + 4 * C) := by sorry
