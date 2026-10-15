-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeDepth_loss_bound
-- name    : ThreeSum.Scales.primeDepth_loss_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:40.206824+00:00
-- url     : https://prove2.me/theorems/9816b615-d949-4ada-bb6b-8626f9f8ab3e
-- title:
--   Finite modulus loss from the selected prime-chain depth
-- statement:
--   Let $R:\mathbb N\to\mathbb N$ be any target-radix function. For $n\in\mathbb N$, put $m=\operatorname{inputBits}(n)$, $y=2^{\lfloor\sqrt m\rfloor+1}$, and $r=\operatorname{ilog}_{4y}(R(n)\mathbin{\mathrm{div}}4)$, where the integer logarithm is zero on argument zero. If a natural number $P$ satisfies $y^r\le P$, then
--
--   $$
--   R(n)\le32y\,4^r P.
--   $$
--
--   The multiplier $32y4^r$ is the construction's declared prime loss. There is no lower-bound assumption on the target $R(n)$.
--
--   This transfers the lower product bound for the actual selected prime chain into a finite comparison with the intended radix, including small input cases.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L410-L432

import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Scales.primeDepth_loss_bound : ∀ (R : Nat → Nat) {n P : Nat}
  (hP :
    @LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.Scales.primeWindow n) (ThreeSum.Scales.primeDepth R n))
      P),
  @LE.le.{0} Nat instLENat (R n)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.Scales.primeLoss R n) P) := by
  sorry
