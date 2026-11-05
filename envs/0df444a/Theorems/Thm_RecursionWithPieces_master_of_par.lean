-- Prove2me | Theorems.Thm_RecursionWithPieces_master_of_par
-- name    : RecursionWithPieces.master_of_par
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:37:42.11402+00:00
-- url     : https://prove2.me/theorems/b4aa8b42-8d5f-4728-8723-71c9131780b7
-- title:
--   Recursion With Pieces: master of par
-- statement:
--   Programs P with parameters (ρ, c), 1/2 ≤ ρ < 1, whose numbers of bits are at most 2λ (`P.m = 1`)
--   and which are polynomial-time (`P.Keeps`), and an x₀ ≥ 18 with 2^x₀ ≥ c + 5, give the conclusion R
--   for the solver made of P, the choice of the
--   level by the program `Pick.pick P x₀`, the precision s(ℓ) = ℓ + 1, and the rates in n and in m with
--   the exponent log₂(1/ρ) of the logarithms. The statement `StEndS R` is a hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L52-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean#L52-L82

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

theorem RecursionWithPieces.master_of_par {R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hEnd : StEndS R) {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) :
    R _ (solverOf P) (Pick.pick P x₀) (fun u => () :: u) (SatK.rN 1 (Real.logb 2 (1 / ρ))) (SatM.rPow (Real.logb 2 (1 / ρ))) := by sorry
