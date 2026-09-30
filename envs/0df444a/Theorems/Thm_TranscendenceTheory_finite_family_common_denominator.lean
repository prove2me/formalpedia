-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_family_common_denominator
-- name    : TranscendenceTheory.finite_family_common_denominator
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T22:10:15.745628+00:00
-- url     : https://prove2.me/theorems/317fab04-be8e-412e-8dac-7b7874aaff39
-- title:
--   Common denominators with uniform numerator degree bounds
-- statement:
--   Let R be a commutative semiring, I a finite index type, and d,N nonnegative integers. For each r∈I let qᵣ∈R[z] have natural degree at most d, and let Hᵣ∈R[[z]] satisfy qᵣHᵣ=1. For each r∈I and 0≤k<N, let Pᵣₖ∈R[z] have natural degree strictly below d(k+1). Put
--
--   $$D(z)=\prod_{r\in I}q_r(z)^N.$$
--
--   Then
--
--   $$\deg D\le dN|I|,$$
--
--   and for every r∈I and 0≤k<N there is a polynomial Aᵣₖ such that
--
--   $$\deg A_{rk}<dN|I|,\qquad D(z)P_{rk}(z)H_r(z)^{k+1}=A_{rk}(z).$$
--
--   Polynomial identities here are read in R[[z]] via the natural inclusion. Natural degree assigns degree zero to the zero polynomial. The assertion includes empty I and N=0; the corresponding conclusions indexed by r or k are then vacuous.
--
--   This gives a common denominator and a uniform numerator degree bound for the whole finite family. It does not require a field, an integral domain, distinct denominators, or pairwise coprimality.
-- source:
--   Derived common-denominator step for https://prove2.me/theorems/1555b7ac-bf6a-43b2-974d-ea1798d3c73b. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/Polynomial/BigOperators.lean (natDegree_prod_le), Degree/Defs.lean (product and power degree bounds), Algebra/BigOperators/Group/Finset/Basic.lean (mul_prod_erase), and RingTheory/PowerSeries/Basic.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/BigOperators.html. Multiply each numerator by the missing denominator factors. The common product has degree at most d*N*card(I), and the new numerators have degree strictly below that uniform bound. The mission application uses d=2 and preserves every interpolation witness, weight and numerical bound.

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem TranscendenceTheory.finite_family_common_denominator
    (R ι : Type*) [CommSemiring R] [Fintype ι]
    (q : ι → Polynomial R) (H : ι → PowerSeries R) (d N : ℕ)
    (hq : ∀ r, (q r).natDegree ≤ d)
    (hH : ∀ r, (q r : PowerSeries R) * H r = 1)
    (P : ι → Fin N → Polynomial R)
    (hP : ∀ r k, (P r k).natDegree < d * (k.val + 1)) :
    let D : Polynomial R := ∏ r, q r ^ N
    D.natDegree ≤ d * N * Fintype.card ι ∧
      ∀ r k, ∃ A : Polynomial R, A.natDegree < d * N * Fintype.card ι ∧
        (D : PowerSeries R) * ((P r k : PowerSeries R) * H r ^ (k.val + 1)) =
          (A : PowerSeries R) := by sorry
