-- Prove2me | Theorems.Thm_Suffices_isKCNF_toN
-- name    : Suffices.isKCNF_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:29:31.032576+00:00
-- url     : https://prove2.me/theorems/96f69827-3094-4dc0-87b0-2d6b52e800e4
-- title:
--   Suffices: is KCNF to N
-- statement:
--   What is read from the code of a 3-CNF without an empty clause is a 3-CNF in the sense of
--   `SparsificationLemma.IsKCNF` (nonempty clauses of at most 3 literals on variables below n). (The
--   case k = 3 of `SparsificationLemma.Mach.isKCNF_toN`, proved here so that this file need not import
--   the files on the Turing machine of Lemma 4.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)

theorem Suffices.isKCNF_toN {n : ℕ} {φ : Sat3.CNF n} (h3 : Sat3.Is3CNF φ) (hnil : [] ∉ φ) : IsKCNF 3 n (Decode.toN φ) := by sorry
