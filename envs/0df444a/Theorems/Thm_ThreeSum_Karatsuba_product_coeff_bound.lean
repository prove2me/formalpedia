-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound
-- name    : ThreeSum.Karatsuba.product_coeff_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:05.479378+00:00
-- url     : https://prove2.me/theorems/4f3df174-db42-4e71-ab03-ad6cf001b13d
-- title:
--   A uniform coefficient bound for integer polynomial products
-- statement:
--   Let $a$ and $b$ be lists of integers, each of length at most $n\in\mathbb N$. Extend their coefficients by zero outside the lists, and assume an integer $U$ bounds the absolute value of every extended coefficient of both lists. This assumption also implies $U\ge0$. Write $A(X)$ and $B(X)$ for the represented polynomials. For every $j\in\mathbb N$,
--
--   $$
--   \bigl|[X^j]\bigl(A(X)B(X)\bigr)\bigr|\le 2nU^2.
--   $$
--
--   The bound covers all degrees, including the implicit zero coefficients beyond the stored product and the case $n=0$.
--
--   This supplies a polynomial integer-magnitude bound for the output coefficients of the verified Karatsuba implementation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/KaratsubaBounds.lean#L86-L110

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Karatsuba.product_coeff_bound : ∀ {as bs : List.{0} Int} {n : Nat} {U : Int} (ha : @LE.le.{0} Nat instLENat (@List.length.{0} Int as) n)
  (hb : @LE.le.{0} Nat instLENat (@List.length.{0} Int bs) n) (hA : ThreeSum.Karatsuba.CoeffBound as U)
  (hB : ThreeSum.Karatsuba.CoeffBound bs U) (j : Nat),
  @LE.le.{0} Int Int.instLEInt
    (@abs.{0} Int instLatticeInt Int.instAddGroup
      (@Polynomial.coeff.{0} Int Int.instSemiring
        (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.{0} Int Int.instSemiring)
          (@Polynomial.{0} Int Int.instSemiring)
          (@instHMul.{0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.instMul.{0} Int Int.instSemiring))
          (ThreeSum.Karatsuba.asPolynomial as) (ThreeSum.Karatsuba.asPolynomial bs))
        j))
    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt n))
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) U
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
