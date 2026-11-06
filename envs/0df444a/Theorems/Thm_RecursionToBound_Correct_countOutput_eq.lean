-- Prove2me | Theorems.Thm_RecursionToBound_Correct_countOutput_eq
-- name    : RecursionToBound.Correct.countOutput_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:20:32.499037+00:00
-- url     : https://prove2.me/theorems/90e1c31b-e393-4508-9ecb-25b41518b370
-- title:
--   Correct: count Output eq
-- statement:
--   The value at a node whose output Φ is a k-CNF on n variables is the number of satisfying
--   assignments of Φ. Hypotheses: i is the index of a level; the Δ of Φ is at most n + 1 and at most
--   `occBound k r`, and n ≥ 29·⌈log₂(2Δ)⌉ + 19; the padding string has at least 2^(`needOutputs`) units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L186-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L186-L202

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


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

theorem RecursionToBound.Correct.countOutput_eq {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (pad : U) (x : CNode) (hΦ : IsKCNF k n (out x))
    (hb : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ occBound k r) (hn : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ n + 1) (hL : 29 * LD (SparsificationLemma.StepSparsify.DeltaOf n (out x)) + 19 ≤ n)
    (hpad : 2 ^ needOutputs S k r (Q.idx l) n ≤ pad.length) : countOutput S k pad (Q.idx l) n x = cntN n (out x) := by sorry
