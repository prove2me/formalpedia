-- Prove2me | Theorems.Thm_RecursionToBound_Correct_walk_eq
-- name    : RecursionToBound.Correct.walk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:55.044976+00:00
-- url     : https://prove2.me/theorems/b282f143-9b9b-483a-8f51-3ce54cd01344
-- title:
--   Correct: walk eq
-- statement:
--   The walk with Calabro's thresholds for α returns the sum of the values at the leaves of the tree
--   whose paths are cut after (32α)^(2k)·n steps. Hypotheses: k ≥ 2, α ≥ k²; ψ is a k-CNF on n variables
--   with at most m clauses; the padding string has at least 2·(number of leaves) − 1 units and at least
--   `stackLenCU k (32α) n m` units;
--   the sum is below 2^(n+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L127-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L127-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Tree
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_RecursionToBound_Correct
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_VariableBound_Net_Main_val
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open PaddedDescent.F.Mark (WfL nSat)
open Groundwork.Sparsify (PFml leaves round)
open RecursionToBound.Correct

theorem RecursionToBound.Correct.walk_eq {α k n m : ℕ} {ψ : PFml} (hk : 2 ≤ k) (hα : k ^ 2 ≤ α) (hψ : IsKCNF k n ψ) (hm : ψ.length ≤ m) (pad : U) (val : CNode → ℕ)
    (h1 : 2 * (leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).length ≤ pad.length + 1)
    (h2 : stackLenCU k (32 * α) n m ≤ pad.length)
    (h3 : ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum < 2 ^ (n + 1)) :
    _root_.StepSparsify.walkSG (Cal.thetaC α) k pad val (rootC (List.replicate n (), ψ)) =
      ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum := by sorry
