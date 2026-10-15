-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:48.33872+00:00
-- url     : https://prove2.me/theorems/cea8a468-7233-4b9a-b496-c21902adcd79
-- title:
--   Computing a bounded linear combination of two arrays
-- statement:
--   Let two length-$n$ stored integer arrays have absolute values at most $U$ and let $|c|\le1$. Suppose each array and the destination fit memory, both sources satisfy the forward-scan safety condition relative to destination, addresses fit words, and $2U$ fits a word. The installed linear body writes $a_i+cb_i$ in its stated time and changes only the destination window.
--
--   This array contract implements the bounded additions and subtractions required by polynomial multiplication.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightArray.lean#L56-L78

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : _root_.ThreeSum.LightArray.SourceSafe srcA dst n) (hsepB : _root_.ThreeSum.LightArray.SourceSafe srcB dst n)
    (hc : |c| ≤ 1) (hword : 2 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (srcA + i)| ≤ U ∧ |μ (srcB + i)| ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (_root_.ThreeSum.LightArray.linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n := by sorry
