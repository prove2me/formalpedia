-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorParameters_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightColorParameters.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:18.879892+00:00
-- url     : https://prove2.me/theorems/e7b3ba32-d159-4234-9451-d05f0347c039
-- title:
--   Execution of coloring-parameter decoding
-- statement:
--   Let $W,t,a\in\mathbb N$ be bit width, coloring index and six-cell destination. Let $\lambda,P,d,\mu$ be limits, program, depth and memory. Suppose the program contains the parameter-decoder and small-division bodies, a nested call is permitted, addresses fit words, $a+6$ fits memory and $t+W+10$ fits a word. The call returns $a$, writes the exact six-field coloring parameter record $\operatorname{data}(W,t)$, uses its specified $t$-dependent time and changes no cell outside those six.
--
--   This constructs coloring parameters from a physical index without assuming supplied parameter rows.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorParameters.lean#L51-L129

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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

namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParameters
end ThreeSum.LightColorParameters
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParameters
end ThreeSum1960614.Machine.ThreeSum.LightColorParameters

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParameters

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d W t free : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum1960614.Machine.ThreeSum.LightColorParameters.meets {pMain pDivide : ℕ} (hp : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorParameters.body pDivide))
    (hdiv : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : free+6 ≤ lim.space)
    (hword : ((t+W+10 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,t,free] μ (_root_.ThreeSum.LightColorParameters.time t)
      (fun result ν => result=(free : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum.ColorParameters.data W t) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν free 6) := by sorry
