-- Prove2me | Theorems.Thm_RecursionWithPieces_master_of_isPieces
-- name    : RecursionWithPieces.master_of_isPieces
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:40:25.951401+00:00
-- url     : https://prove2.me/theorems/a490a638-60c0-436c-ac17-41393e9d5d2f
-- title:
--   Recursion With Pieces: master of is Pieces
-- statement:
--   Pieces (P₀, A, val) with parameters (ρ, c) as Appendix A defines them give the conclusion R for
--   the recursion on `recOf P₀ val c`, the choice of the level by `Pick.pick` with the least x₀ of the
--   theorem on the general recursion, the
--   precision s(ℓ) = ℓ + 1, and the rates with the exponent α' = log₂(1/ρ). The statement `StEndS R` is
--   a hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L89-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L89-L93

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

theorem RecursionWithPieces.master_of_isPieces {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {ρ : ℝ} {c : ℕ} {P₀ : PiecesF}
    {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P₀ A val) :
    R _ (solverOf (Tied.recOf P₀ val c)) (Pick.pick (Tied.recOf P₀ val c) (x₀Of c)) (fun u => () :: u) (SatK.rN 1 (AppRunningTime.alpha' ρ)) (SatM.rPow (AppRunningTime.alpha' ρ)) := by sorry
