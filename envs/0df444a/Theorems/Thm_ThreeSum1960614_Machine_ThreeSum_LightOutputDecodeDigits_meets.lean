-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDigits_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:27.211914+00:00
-- url     : https://prove2.me/theorems/a0035e9d-6556-4e21-9212-e488c0b78281
-- title:
--   Execution of big-endian output-index digit decoding
-- statement:
--   Let $k,J,m,V,b,w\in\mathbb N$, with $m\ge1$ and $k\le V$, and let $\lambda,P,d,\mu$ be limits, program, depth and memory. Suppose the digit wrapper and output-division body occur in $P$; addresses fit words; $d+1$ is strictly below the depth limit; $b+J\le w$; and the stated scratch-space and word bounds fit. The call writes the $J$ base-$m$ digits of $k$ in forward order at $b$, returns
--
--   $$\lfloor k/m^J\rfloor,$$
--
--   meets its stated $(J,V)$ time and preserves every cell below $b$.
--
--   This decodes physical global-output indices in the original block order.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecodeDigits.lean#L42-L142

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDivide_meets
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_reverse

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightOutputDecodeDigits
end ThreeSum.LightOutputDecodeDigits
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOutputDecodeDigits
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.meets {pMain pDivide : ℕ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : _root_.ThreeSum.LightOutputDecodeDigits.space work V ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecodeDigits.word V m J : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,J,m,dst,work] μ (_root_.ThreeSum.LightOutputDecodeDigits.time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((_root_.ThreeSum.OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by sorry
