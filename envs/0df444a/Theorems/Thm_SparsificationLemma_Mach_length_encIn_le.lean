-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_length_encIn_le
-- name    : SparsificationLemma.Mach.length_encIn_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:16.044199+00:00
-- url     : https://prove2.me/theorems/760b7f78-7a31-4256-a468-30f51a4bdc48
-- title:
--   Mach: length enc In le
-- statement:
--   The length of the input plus 8 is at most (s+412)·(n+1)^4, for a 3-CNF on n variables in which
--   no clause is written twice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/LemSparsification.lean#L38-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/LemSparsification.lean#L38-L49

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

theorem SparsificationLemma.Mach.length_encIn_le (s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    (encIn s 3 φ).length + 2 ^ 3 ≤ (s + 412) * (n + 1) ^ 4 := by sorry
