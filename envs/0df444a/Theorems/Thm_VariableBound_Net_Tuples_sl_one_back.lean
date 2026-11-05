-- Prove2me | Theorems.Thm_VariableBound_Net_Tuples_sl_one_back
-- name    : VariableBound.Net.Tuples.sl_one_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:53.918046+00:00
-- url     : https://prove2.me/theorems/90fb5559-5145-4810-b669-1e1c22dc04ab
-- title:
--   Tuples: sl one back
-- statement:
--   The part Π_j of the set put together from (S₀, S) is S j, if S j ⊆ Λ_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L182-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean#L182-L198

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}

theorem VariableBound.Net.Tuples.sl_one_back (S₀ : Finset (Fin D.1.length)) (S : Fin (chks D).length → Finset (Fin D.1.length)) (j : Fin (chks D).length)
    (hS : S j ⊆ (chks D).getD j.val ∅) : sl D 1 j.val (back D S₀ S) = S j := by sorry
