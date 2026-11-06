-- Prove2me | Theorems.Thm_RecursionToBound_Correct_countAll_eq
-- name    : RecursionToBound.Correct.countAll_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:15:14.798947+00:00
-- url     : https://prove2.me/theorems/9aed9b55-000b-429d-9d09-dc1d000c5bf8
-- title:
--   Correct: count All eq
-- statement:
--   «Run Steps 2 to 4 on each of the … outputs and add the results.» For k ≥ 3, a k-CNF φ on n
--   variables without repeated clauses, 0 < r, the index of a level, and a padding string of at least
--   2^(`needOutputs` + `needWalk`) units, `countAll` on (n, φ) is the number of satisfying assignments
--   of φ; provided that every Δ with
--   2 ≤ Δ ≤ `occBound k r` has Δ ≤ n + 1 and n ≥ 29·⌈log₂(2Δ)⌉ + 19.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L232-L302
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Correct.lean#L232-L302

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

theorem RecursionToBound.Correct.countAll_eq {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (φ : CNF n) (pad : U) (hk : 3 ≤ k) (hφ : SatK.IsKCNF k φ)
    (hr1 : 0 < r.1) (hr2 : 0 < r.2) (hΔ : ∀ Δ : ℕ, 2 ≤ Δ → Δ ≤ occBound k r → Δ ≤ n + 1 ∧ 29 * LD Δ + 19 ≤ n)
    (hpad : 2 ^ (needOutputs S k r (Q.idx l) n + needWalk k r n) ≤ pad.length) :
    countAll S k r (Q.idx l) (List.replicate n (), Decode.toN φ) pad = SatK.numSat φ := by sorry
