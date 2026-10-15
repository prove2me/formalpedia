-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWantedRow_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightWantedRow.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:53:07.551808+00:00
-- url     : https://prove2.me/theorems/d2a46950-7a83-423e-b998-152ea615d13e
-- title:
--   Appending a physical wanted-pair row
-- statement:
--   Let $\ell,s,a,n,b,q\in\mathbb N$ denote a left index, right-index source base and start, row length, output base and previously emitted pair count. Let $\lambda,P,d,\mu$ be limits, program, depth and memory with the row body present. Suppose addresses fit words, the source slice ends before $b$, the pair output through $q+n$ fits memory, $\ell$ fits a word and all source values in the slice fit words. The procedure writes
--
--   $$\nu(b+2(q+t))=\ell,\qquad\nu(b+2(q+t)+1)=\mu(s+a+t)\quad(t<n),$$
--
--   within its specified $n$-dependent time, changing only the newly appended $2n$ cells.
--
--   This emits the exact physical matching-pair list without losing repeated original positions.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWantedRow.lean#L33-L82

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightWantedRow
end ThreeSum.LightWantedRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedRow
end ThreeSum1960614.Machine.ThreeSum.LightWantedRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWantedRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 900000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightWantedRow.meets {pMain left src start n dst previous : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedRow.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+start+n ≤ dst) (hspace : dst+2*(previous+n) ≤ lim.space)
    (hleft : (left : ℤ) ≤ lim.word)
    (hvalues : ∀ t < n, |μ (src+start+t)| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [left,src,start,n,dst,previous] μ (_root_.ThreeSum.LightWantedRow.time n)
      (fun _ ν => (∀ t < n, ν (dst+2*(previous+t))=(left : ℤ) ∧
        ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν (dst+2*previous) (2*n)) := by sorry
