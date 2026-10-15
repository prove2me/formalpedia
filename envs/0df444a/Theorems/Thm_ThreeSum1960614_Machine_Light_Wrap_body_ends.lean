-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_Wrap_body_ends
-- name    : ThreeSum1960614.Machine.Light.Wrap.body_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:10:38.877833+00:00
-- url     : https://prove2.me/theorems/88010159-e6c5-4543-95c6-ffc7656c0637
-- title:
--   Executing a benchmark wrapper around a light solver
-- statement:
--   Let $w$ wrap benchmark problem $Q$ into a light task with decision flag $\delta$. Suppose program $P$ at procedure $p$ solves that task with time $T(n,U)$ and needs $N(n,U)$. For bounded input $x$ with $x.n\ge1$, $x.U=x.n^\kappa$, and enough wrapper room, the appended top body starts in the benchmark input memory, reaches the correct answered predicate, and takes at most $T(x.n,x.U)+\operatorname{bodySteps}(\kappa)$.
--
--   This wrapper execution connects the task solver to the benchmark input layout and exact answer predicate.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/TopProcedure.lean#L228-L265

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
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

namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light


namespace Light
end Light
namespace Light.Wrap
end Light.Wrap
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Wrap
end ThreeSum1960614.Machine.Light.Wrap
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.ThreeSum1960614.Machine.Light.Wrap

variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}

theorem ThreeSum1960614.Machine.Light.Wrap.body_ends (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need}
    (hsol : _root_.ThreeSum1960614.Machine.Light.Solves task P p Tn need) (κ : ℕ) (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ)
    {lim : _root_.ThreeSum1960614.Machine.Light.Limits} (hroom : w.Room need x lim) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) 1 (_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec)
      ⟨_root_.Light.frame [0, 0], _root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)⟩ (Tn x.n x.U + w.bodySteps κ) (_root_.ThreeSum1960614.Machine.Light.Wrap.Answered x dec) := by sorry
