-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_table_ends
-- name    : ThreeSum1960614.Machine.Light.Emod.table_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:12:33.569381+00:00
-- url     : https://prove2.me/theorems/c257f36c-cc71-4619-9ee9-4c53c571697e
-- title:
--   Construction of the remainder doubling table
-- statement:
--   Under the remainder routine's precondition for limits $\ell$, positive modulus control $M$, input bound $V$, and scratch base $f$, let $a\le V$. Starting with the prescribed six-local frame, the doubling-table code ends within $$19r(a,M)+6$$ steps, where $r$ is its specified round count. It returns that count and $M2^{r(a,M)}$ and establishes the exact stored doubling-table predicate.
--
--   Accounts for the table-building phase of division-free remainder. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L129-L165

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}

theorem ThreeSum1960614.Machine.Light.Emod.table_ends (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr) (haV : a ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.Light.emodTable ⟨_root_.Light.frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * _root_.Light.emodRounds a Mo + 6) fun σ' =>
      ∃ μ', σ' = ⟨_root_.Light.frame [x, Mo, fr, a, _root_.Light.emodRounds a Mo, ((Mo * 2 ^ _root_.Light.emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
        _root_.ThreeSum1960614.Machine.Light.Emod.Table μ μ' Mo fr (_root_.Light.emodRounds a Mo) := by sorry
