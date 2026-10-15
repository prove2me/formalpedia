-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightClassFilter_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightClassFilter.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:55.828921+00:00
-- url     : https://prove2.me/theorems/a03590a9-9a19-4c21-aa60-a3ab995dad8b
-- title:
--   Filtering one scaled color class
-- statement:
--   Let an integer array $x$ and colors $c(i)<3$ of length $n$ be stored before destination $o$. For wanted color $w<3$, scaling factor $|s|\le1$, values $|x(i)|\le U$, and the stated memory and word bounds, the filter returns and stores the selected-list length, writes the scaled selected items after its header, and changes only the reserved $n+1$ destination cells.
--
--   This filter contract constructs each actual color class and its length header from original input values.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightClassFilter.lean#L59-L127

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightClassFilter.meets {p src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ}
    (hmain : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.body) (x : ℕ → ℤ) (color : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ dst) (hcolors : colors+n ≤ dst) (hspace : dst+(n+1) ≤ lim.space)
    (hwant : want < 3) (hscale : |scale| ≤ 1) (hU : (U : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = x i)
    (hcolorRead : ∀ i < n, μ (colors+i) = (color i : ℤ))
    (hcolorLt : ∀ i < n, color i < 3) (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src,colors,dst,n,want,scale] μ (_root_.ThreeSum.LightClassFilter.time n)
      (fun r ν => r = ((_root_.ThreeSum.LightClassFilter.items x color want scale n).length : ℤ) ∧
        ν dst = ((_root_.ThreeSum.LightClassFilter.items x color want scale n).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+1) (_root_.ThreeSum.LightClassFilter.items x color want scale n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (n+1)) := by sorry
