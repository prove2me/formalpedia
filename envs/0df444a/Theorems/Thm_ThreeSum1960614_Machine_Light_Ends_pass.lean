-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
-- name    : ThreeSum1960614.Machine.Light.Ends.pass
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:22:50.088264+00:00
-- url     : https://prove2.me/theorems/2deb1839-d36c-4667-8774-58524a21d14f
-- title:
--   A bounded memory-writing pass
-- statement:
--   Let a Light pass run $n$ rounds with counter local $c$, length local $x$, destination local $y$, and expression $e$. Suppose each round safely evaluates $e$ to the specified value $f(j)$ in the partially written memory; the final frame and memory satisfy $Q$; addresses fit the word bound; the output interval fits space; and $x,y\ne c$. If $$n(\operatorname{cost}(e)+12)+6\le T,$$ the pass reaches $Q$ within $T$ steps.
--
--   Gives the exact costed rule for array-writing scans. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L43-L69

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
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe

namespace Light
end Light
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

theorem ThreeSum1960614.Machine.Light.Ends.pass {c x y n T : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} {loc : ℕ → ℤ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, _root_.Light.wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, _root_.Light.wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, _root_.Light.wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by (first
                                           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                               first
                                               | omega
                                               | (ring_nf; omega))
                                           | omega
                                           |
                                             (simp [] <;>
                                                 first
                                                 | omega
                                                 | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.pass c (_root_.ThreeSum1960614.Machine.Light.v x) (_root_.ThreeSum1960614.Machine.Light.v y) e) ⟨loc, μ⟩ T Q := by sorry
