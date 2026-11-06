-- Prove2me | Theorems.Thm_PiecesCounted_oracleFromAlgorithm
-- name    : PiecesCounted.oracleFromAlgorithm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:24:58.756023+00:00
-- url     : https://prove2.me/theorems/711e16d9-e877-4fcd-846f-966a65078f6b
-- title:
--   Pieces Counted: oracle From Algorithm
-- statement:
--   Proof of `OracleFromAlgorithm`: the substitution `stSubstWithin` puts the answering machine
--   `passOrRun Alg` in place of the oracle, and each answer stays within its price.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Oracle.lean#L44-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Oracle.lean#L44-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Oracle
set_option autoImplicit false
section
section
open PiecesCounted
open Groundwork QueryMachines

theorem PiecesCounted.oracleFromAlgorithm : OracleFromAlgorithm := by sorry
