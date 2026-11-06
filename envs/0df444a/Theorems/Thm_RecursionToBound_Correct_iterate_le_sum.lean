-- Prove2me | Theorems.Thm_RecursionToBound_Correct_iterate_le_sum
-- name    : RecursionToBound.Correct.iterate_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:06.129392+00:00
-- url     : https://prove2.me/theorems/e70b782e-47ac-4ce5-b1d2-17f1670ef948
-- title:
--   Correct: iterate le sum
-- statement:
--   The number after any number of rounds is at most the sum of the values of the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L101-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L101-L104

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
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_step
import Theorems.Thm_ClauseBound_Part_Lower_step
import Theorems.Thm_CountKSatRate_Top_iterate_le_sum
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_PaddedDescent_F_Arith_Inv_step
import Theorems.Thm_VariableBound_Net_Main_val
import Theorems.Thm_WidthK_InvK_step
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

theorem RecursionToBound.Correct.iterate_le_sum {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by sorry
