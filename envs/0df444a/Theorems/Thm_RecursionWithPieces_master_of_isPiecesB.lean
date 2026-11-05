-- Prove2me | Theorems.Thm_RecursionWithPieces_master_of_isPiecesB
-- name    : RecursionWithPieces.master_of_isPiecesB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:40:07.761392+00:00
-- url     : https://prove2.me/theorems/a6a859a7-b879-4c23-b7cd-8acc669309ea
-- title:
--   Recursion With Pieces: master of is Pieces B
-- statement:
--   The pieces of Appendix B, with the constant c, give the conclusion R for `solverAB`, `pickAB`,
--   `prec` and the rates log₂ log₂(n+4)/√(log₂(n+4)) and 1/√(log₂(m+2)). The statement `StEndS R` is a
--   hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L98-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L98-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_UniformInK_Top_FallBack
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_RecursionWithPieces_Master
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.Both UniformInK VariableBound GeneralPieces

theorem RecursionWithPieces.master_of_isPiecesB {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : Tied.IsPiecesB c P₀ A val) :
    R _ (solverAB P₀ val c) (pickAB P₀ val c) prec (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) := by sorry
