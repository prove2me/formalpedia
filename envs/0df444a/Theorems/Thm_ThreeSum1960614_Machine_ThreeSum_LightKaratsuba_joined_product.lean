-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_joined_product
-- name    : ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:31:07.065301+00:00
-- url     : https://prove2.me/theorems/7159d4d8-b38e-40a2-ac09-49bf8ae78fdd
-- title:
--   Karatsuba recombination recovers product coefficients
-- statement:
--   Let integer lists $a,b$ have length $n=2h$. If three workspace blocks store the low-half product, high-half product, and product of half-sums, then for every $j$ the recombined value equals $$[X^j](A(X)B(X)).$$
--
--   This identity connects the stored three-product recombination to the polynomial coefficients required by cyclic correlation.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightKaratsuba.lean#L341-L379

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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

namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial

theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ work half (as.take half) (bs.take half))
    (h2 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ (work + 2 * n) half
      (_root_.ThreeSum.Karatsuba.plus (as.take half) (as.drop half)) (_root_.ThreeSum.Karatsuba.plus (bs.take half) (bs.drop half)))
    (j : ℕ) : _root_.ThreeSum.LightKaratsuba.joined μ work n half j = (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j := by sorry
