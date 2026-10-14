-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_joined_product
-- name    : ThreeSum.LightKaratsuba.joined_product
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:44:14.395403+00:00
-- url     : https://prove2.me/theorems/289e3b39-c82f-4645-898a-62bbb461fb12
-- title:
--   Karatsuba joining reconstructs every product coefficient
-- statement:
--   Let $A,B$ be integer coefficient lists of common length $n=2h$, split into lower and upper halves with polynomials $A_0,A_1,B_0,B_1$. Suppose memory $\mu$ stores the $n$-cell coefficient arrays for $Z_0=A_0B_0$, $Z_2=A_1B_1$, and $Z_m=(A_0+A_1)(B_0+B_1)$ at addresses $w,w+n,w+2n$. Let $J_j$ be the joining expression using these arrays with shifts $0,h,n$ and zero outside each window. Then, for every $j\in\mathbb N$,
--
--   $$J_j=[X^j]\bigl(Z_0+X^h(Z_m-Z_0-Z_2)+X^nZ_2\bigr)=[X^j]\bigl(A(X)B(X)\bigr).$$
--
--   This is the coefficient identity used by the concrete joining passes of the Karatsuba procedure.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightKaratsuba.lean#L341-L379

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
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
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

theorem ThreeSum.LightKaratsuba.joined_product : ∀ {μ : Nat → Int} {work n half : Nat} {as bs : List.{0} Int}
  (hhalf :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) half)
      n)
  (ha : @Eq.{1} Nat (@List.length.{0} Int as) n) (hb : @Eq.{1} Nat (@List.length.{0} Int bs) n)
  (h0 : ThreeSum.LightKaratsuba.ProductAt μ work half (@List.take.{0} Int half as) (@List.take.{0} Int half bs))
  (h2 :
    ThreeSum.LightKaratsuba.ProductAt μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work n) half
      (@List.drop.{0} Int half as) (@List.drop.{0} Int half bs))
  (hm :
    ThreeSum.LightKaratsuba.ProductAt μ
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      half (ThreeSum.Karatsuba.plus (@List.take.{0} Int half as) (@List.drop.{0} Int half as))
      (ThreeSum.Karatsuba.plus (@List.take.{0} Int half bs) (@List.drop.{0} Int half bs)))
  (j : Nat),
  @Eq.{1} Int (ThreeSum.LightKaratsuba.joined μ work n half j)
    (@Polynomial.coeff.{0} Int Int.instSemiring
      (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.{0} Int Int.instSemiring)
        (@Polynomial.{0} Int Int.instSemiring)
        (@instHMul.{0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.instMul.{0} Int Int.instSemiring))
        (ThreeSum.Karatsuba.asPolynomial as) (ThreeSum.Karatsuba.asPolynomial bs))
      j) := by
  sorry
