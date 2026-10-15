-- Prove2me | Theorems.Thm_ThreeSum_LightSwitchScalar_scalar_safe
-- name    : ThreeSum.LightSwitchScalar.scalar_safe
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:27:59.002078+00:00
-- url     : https://prove2.me/theorems/bd981fa6-f13d-4504-a917-f0e653550b57
-- title:
--   Structural word safety for bounded scalar expression trees
-- statement:
--   Let $B\in\mathbb N$ satisfy $B\ge2$, and let $\sigma$ be a machine state whose every local variable has absolute value at most $B$. Let $e$ be an expression built from natural literals at most $B$, local variables, and addition, subtraction, or multiplication, with no memory loads. Write $c(e)$ for its syntax-tree cost, charging one for each leaf and operation. If the machine's word-magnitude limit is $W$ and $B^{c(e)}\le W$, then
--
--   $$
--   e\text{ is safe to evaluate in }\sigma\text{ under the machine limits}.
--   $$
--
--   Safety includes the bounds required for all intermediate arithmetic expressions.
--
--   This gives a reusable structural check for the fixed scalar formulas implementing the cubic switch.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSwitchScalar.lean#L62-L76

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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

theorem ThreeSum.LightSwitchScalar.scalar_safe : ∀ {lim : Light.Limits} {B : Nat}
  (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) B) (σ : Light.State)
  (hvars :
    ∀ (i : Nat),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (σ.loc i))
        (@Nat.cast.{0} Int instNatCastInt B))
  (e : Light.Expr) (he : ThreeSum.LightSwitchScalar.Small B e)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B e.cost))
      lim.word),
  Light.Expr.Safe lim σ e := by
  sorry
