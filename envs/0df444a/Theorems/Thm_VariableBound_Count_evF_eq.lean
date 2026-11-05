-- Prove2me | Theorems.Thm_VariableBound_Count_evF_eq
-- name    : VariableBound.Count.evF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:49:45.65424+00:00
-- url     : https://prove2.me/theorems/8a0adc1f-6525-4dc6-b266-c1e66c081238
-- title:
--   Count: ev F eq
-- statement:
--   If the list 𝓛 is fit for an evaluation, M ≥ β − 1 + r, M ≥ n + r and X(𝓛) = 0, the program's
--   F(𝓛) is the number of satisfying assignments. Further hypotheses: the statements on the evaluation,
--   on the number of
--   profiles and display (63); a correct solver with K ≥ 2; the pad fits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L139-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L139-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

theorem VariableBound.Count.evF_eq (hEv : Net.StEvXF) (hNP : Net.StNPrMax) (hProd : AppVariables.ProductStmt) {ok : Idx → Prop} (hC : S.Correct ok) {k : ℕ} {pad : U} {i : Idx} {n Δ nb M : ℕ} {ψ : Fml}
    {L : List (List ℕ)} (hok : ok i) (hK : 2 ≤ S.K i) (hfit : FitsD S k i n Δ pad.length) (hF : Fit k n Δ nb M (ψ, L)) (h1 : beta n ψ.length nb - 1 + L.length ≤ M)
    (h2 : n + L.length ≤ M) (h0 : Xsum (Vof (n := n) ψ) nb (chksD ψ.length L) = 0) : (evF S k pad i n Δ nb M (ψ, L)).toNat = nSat n ψ := by sorry
