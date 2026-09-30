-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_coordinate_power_recurrence
-- name    : WeierstrassEllipticZeta.finite_coordinate_power_recurrence
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T20:48:31.830338+00:00
-- url     : https://prove2.me/theorems/cd0420d6-3366-4a92-9457-351f310f878a
-- title:
--   Finite coordinate values give uniform power recurrences
-- statement:
--   Let K be a field, σ a variable set with decidable equality, i a coordinate, T a finite subset of K, and N,b natural numbers with N|T| ≤ b+1. There exists a multivariate polynomial r supported on exponents at most b times the i-th unit vector such that the following holds simultaneously for every evaluation point v with v(i) in T and every ideal I containing the N-th power of the evaluation kernel at v:
--
--   $$X_i^{b+1}-r\in I.$$
--
--   The same r works for all such points and ideals. No finiteness assumption on σ and no positivity assumption on N or nonemptiness assumption on T is needed.
-- source:
--   Derived finite-coordinate-value sufficient criterion for the frontier https://prove2.me/theorems/719a9dcd-3d98-4eb4-a179-dc77f9aa6a0d. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The generic construction is derived using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/Polynomial/BigOperators.lean (natDegree_finsetProd_X_sub_C_eq_card), Algebra/Polynomial/Degree/IsMonicOfDegree.lean (exists_natDegree_lt), Algebra/MvPolynomial/Equiv.lean (toMvPolynomial, eval_toMvPolynomial), and RingTheory/Ideal/Operations.lean (pow_mem_pow). The uniform geometric estimate with the new sufficient coordinate-value count condition remains open; equivalence to arbitrary coordinate recurrences is not asserted.

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

open scoped Classical

noncomputable section

theorem WeierstrassEllipticZeta.finite_coordinate_power_recurrence
    (K σ : Type*) [Field K] [DecidableEq σ]
    (i : σ) (T : Finset K) (N b : ℕ)
    (hfit : N * T.card ≤ b + 1) :
    ∃ r : MvPolynomial σ K,
      (∀ e ∈ r.support, e ≤ Finsupp.single i b) ∧
      ∀ (v : σ → K), v i ∈ T →
        ∀ I : Ideal (MvPolynomial σ K),
          RingHom.ker (MvPolynomial.eval v) ^ N ≤ I →
            MvPolynomial.X i ^ (b + 1) - r ∈ I := by sorry
