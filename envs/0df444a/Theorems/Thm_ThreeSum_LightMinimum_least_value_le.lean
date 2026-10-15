-- Prove2me | Theorems.Thm_ThreeSum_LightMinimum_least_value_le
-- name    : ThreeSum.LightMinimum.least_value_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:33:17.527388+00:00
-- url     : https://prove2.me/theorems/ae1716ea-bea3-4cf9-87cc-49927a680551
-- title:
--   The running minimum is no larger than any inspected value
-- statement:
--   Let $f:\mathbb N\to\mathbb Z$. Define the running-minimum index $m_0=0$ and, recursively, $m_{n+1}=n$ if $f(n)<f(m_n)$, with $m_{n+1}=m_n$ otherwise. For natural numbers $i<n$,
--
--   $$f(m_n)\le f(i).$$
--
--   The strict update rule keeps the previous index when values tie. This establishes the value comparison needed for the minimum-selection routine.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMinimum.lean#L36-L51

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightMinimum.least_value_le : ∀ (f : Nat → Int) (n i : Nat) (hi : @LT.lt.{0} Nat instLTNat i n),
  @LE.le.{0} Int Int.instLEInt (f (ThreeSum.LightMinimum.least f n)) (f i) := by
  sorry
