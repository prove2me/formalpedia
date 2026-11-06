-- Prove2me | Theorems.Thm_VariableBound_ArithNeed_needD_le_sum
-- name    : VariableBound.ArithNeed.needD_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:38.795975+00:00
-- url     : https://prove2.me/theorems/ec9819b3-cf61-4594-b5f8-59b9b7598e25
-- title:
--   Arith Need: need D le sum
-- statement:
--   The exponent is at most the sum of its parts, if 2^β ≤ n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNeed.lean#L64-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNeed.lean#L64-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNeed
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNeed
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL UniformInK VariableBound.Net

theorem VariableBound.ArithNeed.needD_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {k n s : ℕ} (hD : 2 ^ betaU k s ≤ n + 1) :
    needD S k i n s ≤ 3 * S.K i ^ 8 * (S.K i).size + PbD (S.K i) n (2 ^ betaU k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n)) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) +
      (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size)) + n / 2 ^ s := by sorry
