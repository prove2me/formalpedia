-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero
-- name    : WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/ab888872-40a1-5768-be05-3d7f609466d6
-- title:
--   Transcendental element in a valuation ring over a characteristic-0 field
-- statement:
--   Let $k$ be a field of characteristic $0$, in an arbitrary universe. The assertion is the existence of the following data, with $L$ in the same universe as $k$: a type $L$ carrying a field structure, which is algebraically closed and of characteristic $0$; a valuation subring $A$ of $L$; a ring homomorphism $\varphi : k \to L$ whose values all lie in $A$; and a ring homomorphism $\iota : k \to A/\mathfrak m_A$ into the residue field of the local ring $A$, such that for every $a \in k$ the residue class of the element $\varphi(a)$ of $A$ equals $\iota(a)$ — so $\iota$ is the reduction of $\varphi$. Moreover there is an element $t \in L$ lying in $A$ whose class in $A$ belongs to the maximal ideal $\mathfrak m_A$, and which is transcendental over $k$ through $\varphi$ in the strong sense that for every nonzero polynomial $P \in k[X]$ the value $P^{\varphi}(t)$, obtained by applying $\varphi$ to the coefficients and substituting $t$, is nonzero. (Injectivity of $\varphi$ is not stated, but follows from the last condition applied to constant polynomials.)
--
--   This is the equal-characteristic-$0$ analogue of a Witt-vector lifting datum: a characteristic-$0$ field embeds into the residue field of a valuation ring of an algebraically closed field whose maximal ideal contains an element transcendental over it, as provided classically by Chevalley's extension theorem for places. It is used in the treatment of the modular equation with multiplicities, where a curve over $k$ is deformed by $t$ inside $A$ so that the generic fibre has transcendental $j$-invariant while the reduction recovers the original curve; it is cited by [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental) and [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial WeierstrassCurve

universe u

theorem WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero
    (k : Type u) [Field k] [CharZero k] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : k →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : k →+* IsLocalRing.ResidueField A),
      (∀ a : k, IsLocalRing.residue A ⟨φ a, hφ a⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial k, P ≠ 0 → P.eval₂ φ t ≠ 0 := by sorry
