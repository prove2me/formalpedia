-- Prove2me | Theorems.Thm_ThreeSum_Scales_scoreLoss_finite_bound
-- name    : ThreeSum.Scales.scoreLoss_finite_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:43.210452+00:00
-- url     : https://prove2.me/theorems/5bfdc82d-4d6e-45d1-817d-499366b6a7e4
-- title:
--   Finite transfer from prime-chain contraction to accumulated score loss
-- statement:
--   Fix $k,n,H,H_1,P\in\mathbb N$. Let $m=\operatorname{inputBits}(n)$, $y=\operatorname{primeWindow}(n)$, and $r=\operatorname{primeDepth}(R,n)$ for the constructed radix $R$. Let $C$ count the primes in $(y,4y]$ and let $D=\operatorname{ilog}_y(3n^k)$ be the divisor budget. Assume
--
--   $$
--   C>0,\quad Dy\le4C(k+2)(m+1),\quad
--   C^rH\le D^rH_1,\quad P\le(4y)^r.
--   $$
--
--   Then
--
--   $$
--   PH\le\bigl(16(k+2)(m+1)\bigr)^rH_1.
--   $$
--
--   The power on the right is the explicit accumulated score loss. The theorem converts finite candidate-density, contraction, and modulus bounds into a bound on the final modulus-weighted score.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L702-L735

import Definitions.Def_ThreeSum1962Source_Bundle05
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

theorem ThreeSum.Scales.scoreLoss_finite_bound : ∀ {k n H H₁ P : Nat}
  (hC :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n))))
  (hbudget :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.Scales.divisorBudget k n)
        (ThreeSum.Scales.primeWindow n))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  (hcontract :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n)))
          (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
        H)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.Scales.divisorBudget k n) (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
        H₁))
  (hP :
    @LE.le.{0} Nat instLENat P
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (ThreeSum.Scales.primeWindow n))
        (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))),
  @LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) P H)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.Scales.scoreLoss k n) H₁) := by
  sorry
