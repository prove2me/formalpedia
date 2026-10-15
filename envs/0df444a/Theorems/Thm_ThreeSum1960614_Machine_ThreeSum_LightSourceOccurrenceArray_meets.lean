-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceOccurrenceArray_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:28.339135+00:00
-- url     : https://prove2.me/theorems/5e5b9870-65ed-4838-8c84-0b01d5663824
-- title:
--   Execution of the complete occurrence-code row array
-- statement:
--   Let $N,J,m,b,w\in\mathbb N$ with $m\ge1$ and let $\lambda,P,d,\mu$ be limits, program, depth and memory. Suppose the wrapper, digit decoder and division bodies occur in $P$; addresses fit words; $b+NJ\le w$; the digit decoder’s explicit space bound for magnitude $N$ and word bound for $(N,m,J)$ fit; and $d+2$ is strictly below the depth limit. The procedure writes
--
--   $$\nu(b+iJ+j)=\operatorname{digit}_{m,J}(i,j)\qquad(i<N,\ j<J),$$
--
--   where digits are in forward block order. It meets its stated $(N,J)$ time and preserves all cells below $b$.
--
--   This constructs the occurrence-index arrays needed by reusable source banks.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L33-L82

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDigits_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceOccurrenceArray
end ThreeSum.LightSourceOccurrenceArray
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceOccurrenceArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.meets {pMain pDigits pDivide : ℕ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceOccurrenceArray.body pDigits))
    (hdigits : P[pDigits]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body)
    {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : _root_.ThreeSum.LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [N,J,m,dst,work] μ (_root_.ThreeSum.LightSourceOccurrenceArray.time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((_root_.ThreeSum.OutputDecodeOrder.indices m J i).getD j 0 : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by sorry
