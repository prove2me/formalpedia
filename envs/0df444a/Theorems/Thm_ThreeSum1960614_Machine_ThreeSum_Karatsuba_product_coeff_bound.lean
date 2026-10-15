-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Karatsuba_product_coeff_bound
-- name    : ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:17:05.591574+00:00
-- url     : https://prove2.me/theorems/8528d2c8-becc-4afa-b421-1c48d48184a4
-- title:
--   A coefficient bound for polynomial multiplication
-- statement:
--   Let integer lists $a,b$ have length at most $n$ and coefficient bound $U$. Every coefficient of their polynomial product satisfies $$|[X^j](A(X)B(X))|\le2nU^2\qquad(j\in\mathbb N).$$
--
--   This coefficient estimate supplies a safe word bound for the concrete Karatsuba product and its intermediate arrays.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/KaratsubaBounds.lean#L86-L110

import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

open _root_.Polynomial
open scoped _root_.BigOperators

theorem ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs U) (j : ℕ) :
    |(_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by sorry
