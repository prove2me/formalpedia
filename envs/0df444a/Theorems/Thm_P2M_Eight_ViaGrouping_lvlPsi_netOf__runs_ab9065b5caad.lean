-- Prove2me | Theorems.Thm_P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad
-- name    : P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:38.432146+00:00
-- url     : https://prove2.me/theorems/9953bf9b-73cf-4b7c-9b3e-a0e400ebd4d5
-- title:
--   P2 M Eight Via Grouping lvl Psi net Of  runs ab9065b5caad: P2 M Eight Via Grouping lvl Psi net Of  runs ab9065b5caad
-- statement:
--   Definition 2(iii) for Ψ: the function for Ψ, run as a procedure, answers every query on settings
--   of the network of ι in one step, on states of size at most `lvlPsiSize g`·(size of c + B + λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L106-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L106-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

theorem P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad {C : Type} [HasSize C] {g : ℕ} {tr : Bool} {psi : ℕ → ℕ → PsiQ → ℤ} (hΨ : StPsiOK g tr psi) (lam : C → ℕ) (c : C) {y B : ℕ}
    {Rm : Inst (Fin (g * g)) (List Bool)} (hl : 1 ≤ lam c) (hy : y < (tOf (lam c) + 1) ^ nRect g) (hR : BoundedInst (lam c) B Rm) (a b : Fin (nParts g g tr)) (hab : a ≠ b)
    {z z' : List Bool} (hz : z ∈ (netOfι g tr (lam c) y Rm).S a) (hz' : z' ∈ (netOfι g tr (lam c) y Rm).S b) :
    (ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a.val, b.val), (z, z'))) 1 (lvlPsiSize g * (size c + B + lam c))
      ((netOfι g tr (lam c) y Rm).Ψ a b z z') := by sorry

alias «Eight».«ViaGrouping».«lvlPsi_netOfι_runs» := P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad
