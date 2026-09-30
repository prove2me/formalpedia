-- Prove2me | Theorems.Thm_TranscendenceTheory_pure_power_standard_monomial_basis
-- name    : TranscendenceTheory.pure_power_standard_monomial_basis
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T05:32:02.188592+00:00
-- url     : https://prove2.me/theorems/59cb8f12-d4f7-4f7f-ba02-e645e5402da4
-- title:
--   Standard monomial basis and exact dimension for pure leading powers
-- statement:
--   Let $K$ be a field and let $R=K[x_i:i\in\sigma]$, where $\sigma$ is finite. Fix a monomial order, nonnegative integers $d_i$, and polynomials $b_i$ whose leading coefficients are units and whose leading exponent vectors are $d_i e_i$. Put $J=(b_i:i\in\sigma)$.
--
--   The residue classes of the monomials
--
--   $$\prod_{i\in\sigma}x_i^{a_i},\qquad 0\leq a_i<d_i,$$
--
--   form a $K$-basis of $R/J$. In particular, this quotient is finite-dimensional and
--
--   $$\dim_K(R/J)=\prod_{i\in\sigma}d_i.$$
--
--   Every polynomial $f$ has a unique representative $r$ modulo $J$ whose support lies in this exponent box. Equivalently, $f-r\in J$, and every exponent $a$ appearing in $r$ satisfies $a_i<d_i$ for every $i$.
--
--   No algebraic-closure or radical-ideal assumption is required. Zero exponents are allowed: in that case the basis is empty and the quotient is zero. If there are no variables, the empty product is one and the quotient is $K$.
-- source:
--   Derived pure-power case of the standard-monomial basis theorem. The usual background is the product criterion for relatively prime leading monomials: John Edward Perry, Combinatorial Criteria for Groebner Bases (2005 thesis), section 2.4, Theorem 2.4, pp. 59-60, https://repository.lib.ncsu.edu/server/api/core/bitstreams/8b3d0e6c-fd44-4a52-82ee-39c6da4f6703/content. The Lean proof independently establishes the special pure-power leading-divisibility criterion by induction on the generators, using MonomialOrder.div in pinned Mathlib, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/MvPolynomial/Groebner.lean. This gives an explicit exponent-box basis, unique reduced representatives, and dim_K(R/(b_i)) = product_i d_i over any field, including zero exponents and the empty variable set. It strengthens the earlier quotient-dimension upper bound; it does not prove a full multihomogeneous Bezout theorem. The A.1 application replaces the exponent-product budget in https://prove2.me/theorems/aae7ee1d-79e8-444d-9ac1-03a2ab38cb18 by the exactly equal quotient dimension. Both directions preserve C and all witnesses. Selecting the equations and primes and proving the uniform bidegree bound remain Open.

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

noncomputable section
open MvPolynomial
open scoped MonomialOrder

theorem TranscendenceTheory.pure_power_standard_monomial_basis
    (K σ : Type*) [Field K] [Fintype σ]
    (o : MonomialOrder σ) (d : σ → ℕ) (b : σ → MvPolynomial σ K)
    (hu : ∀ i, IsUnit (o.leadingCoeff (b i)))
    (hd : ∀ i, o.degree (b i) = Finsupp.single i (d i)) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span (Set.range b)
    Module.Finite K (MvPolynomial σ K ⧸ J) ∧
      (∃ β : Module.Basis (∀ i, Fin (d i)) K (MvPolynomial σ K ⧸ J),
        ∀ a, β a = Ideal.Quotient.mk J
          (monomial (Finsupp.equivFunOnFinite.symm (fun i => (a i).val)) 1)) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) = ∏ i, d i ∧
      ∀ f : MvPolynomial σ K, ∃! r,
        (∀ c ∈ r.support, ∀ i, c i < d i) ∧ f - r ∈ J := by sorry
