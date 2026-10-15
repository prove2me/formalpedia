-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverGreedy_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:15.270758+00:00
-- url     : https://prove2.me/theorems/9708f601-bd9c-4413-b865-3c593aed4f21
-- title:
--   Executing the deterministic greedy cover schedule
-- statement:
--   Let a stored Boolean matrix have positive row count $r$, column count $c$, and requested round count $t$. Suppose the active-vector allocation follows the matrix, the full greedy workspace fits, addresses and one fit words, and helper placement and depth bounds hold. The program writes exactly the semantic greedy-choice list and final active vector, returns the choice-list base, and changes only its designated greedy workspace within the stated time.
--
--   This theorem identifies the executed greedy choices and final active vector with their finite semantic counterparts.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCoverGreedy.lean#L62-L180

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverScores_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverUpdate_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMinimum_meets
import Theorems.Thm_ThreeSum_BooleanGreedy_active_succ
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSum.LightCoverGreedy
end ThreeSum.LightCoverGreedy
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
end ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy
end ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCoverGreedy
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BooleanGreedy
open _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+_root_.ThreeSum.LightCoverGreedy.total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,activePtr,rows,cols,rounds] μ (_root_.ThreeSum.LightCoverGreedy.time rows cols rounds)
      (fun r μ' => r = (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols) ((_root_.ThreeSum.BooleanGreedy.choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (_root_.ThreeSum.BooleanGreedy.active matrix rows cols rounds j : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' activePtr (_root_.ThreeSum.LightCoverGreedy.total rows cols rounds)) := by sorry
