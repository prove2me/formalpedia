-- Prove2me | Theorems.Thm_SparsifyThenCount_stAlgSG
-- name    : SparsifyThenCount.stAlgSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:18.38603+00:00
-- url     : https://prove2.me/theorems/e7915a45-8202-490b-85e8-1e30aec8cea2
-- title:
--   Sparsify Then Count: st Alg SG
-- statement:
--   For thresholds Θ that serve (with the bound Lc) and a solver with a sequence of levels: the
--   merged function for Θ and its exponent function are an algorithm for the rates rn and rm. Given: the
--   merged function is right (`StCorrectBDG`), it and the exponent function are polynomial-time
--   (`StCertBDG`), the exponent is at most those of the two algorithms merged (`StExpBD`), and the two
--   inequalities for the number of steps
--   (`StTimeD`, `StTimeM`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Tied.lean#L36-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Tied.lean#L36-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_SparsifyThenCount_Tied
set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound VariableBound.Decide

theorem SparsifyThenCount.stAlgSG (hC : StCorrectBDG) (hK : StCertBDG) (hE : StExpBD) (hTD : StTimeD) (hTM : ClauseBound.Both.StTimeM) (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) (hΘ : StepSparsify.Serves Θ Lc) :
    StAlgSG Θ := by sorry
