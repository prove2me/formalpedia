-- Prove2me | Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
-- name    : ThreeSum.LocalCoverBounds.pow_le_choose_mul
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:40:14.055819+00:00
-- url     : https://prove2.me/theorems/9a5d3b13-d43c-4671-ba32-cf0022a29bba
-- title:
--   A binomial lower bound from disjoint coordinate blocks
-- statement:
--   For arbitrary natural numbers $c$ and $r$,
--
--   $$
--   c^r\le \binom{cr}{r}.
--   $$
--
--   The right side counts all subsets of size $r$ in a set of $cr$ positions. The left side counts choices of one position in each of $r$ labeled blocks, each containing $c$ positions. The assertion also includes $c=0$ and $r=0$, with the usual natural-number conventions for powers and binomial coefficients.
--
--   This exact finite estimate supplies a lower bound for the number of local subset outputs without using asymptotic factorial estimates.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalCoverBounds.lean#L34-L62

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.LocalCoverBounds.pow_le_choose_mul : ∀ (c r : Nat),
  @LE.le.{0} Nat instLENat
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) c r)
    ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c r).choose r) := by
  sorry
