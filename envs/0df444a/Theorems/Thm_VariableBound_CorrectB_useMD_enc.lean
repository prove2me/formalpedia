-- Prove2me | Theorems.Thm_VariableBound_CorrectB_useMD_enc
-- name    : VariableBound.CorrectB.useMD_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:55:09.730997+00:00
-- url     : https://prove2.me/theorems/25a662a9-4d22-43bd-8474-e6e4ebc62251
-- title:
--   Correct B: use MD enc
-- statement:
--   On the code of (k, φ), k ≥ 1, φ a k-CNF, the algorithm for the bound in m is taken exactly if
--   every variable occurs, there is a clause, and its exponent is not the larger one. Given
--   `UniformInK.StAllOccU` and `StDecM`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/CorrectB.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/CorrectB.lean#L29-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Top_CorrectB
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.CorrectB
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK

theorem VariableBound.CorrectB.useMD_enc (hA : StAllOccU) (hD : StDecM) {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pick : U → U × Idx) (slU : U → U) {n : ℕ} (φ : Sat3.CNF n)
    (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    useMD S pick slU (SatM.enc k φ) = true ↔
      SatM.AllOccur φ ∧ 1 ≤ φ.length ∧ eM S pick (SatM.enc k φ) ≤ eD S pick slU (SatM.enc k φ) := by sorry
