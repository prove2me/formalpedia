-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:11:14.5326+00:00
-- url     : https://prove2.me/theorems/40d79752-f251-433d-89e6-91789d99fa38
-- title:
--   Sorting and deduplicating one separated color class
-- statement:
--   Let integer list $L$ be stored at the source, with a disjoint later destination and scratch after both length-$|L|$ reservations. Under the concrete normalization interface, space and word bounds, and sufficient depth for sort and dedup recursion, the routine returns a strictly increasing list $S$ with $$|S|\le|L|,\qquad z\in S\iff z\in L.$$ It stores $S$ at the destination within its stated time and preserves cells below scratch outside the source and destination reservations.
--
--   Removes duplicates within a color class while preserving exactly its original membership witnesses. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightNormalize.lean#L143-L170

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_sort_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_dedup_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightNormalize
end ThreeSum.LightNormalize
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightNormalize
end ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightNormalize
open _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets {pMain src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : _root_.ThreeSum1960614.Machine.Light.Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : _root_.ThreeSum.LightNormalize.space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,L.length,dst,work] μ (_root_.ThreeSum.LightNormalize.time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) := by sorry
