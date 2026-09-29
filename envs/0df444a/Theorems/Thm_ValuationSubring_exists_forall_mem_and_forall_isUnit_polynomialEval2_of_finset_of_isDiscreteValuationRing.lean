-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
-- name    : ValuationSubring.exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0e801a02-473c-5802-9e99-8db25cc5027e
-- title:
--   Common geometric element for finitely many discrete valuation subrings
-- statement:
--   Let $A_0$ be a commutative ring, $F_0$ a field, $j_0 : A_0 \to F_0$ a ring homomorphism, and $V$ a finite set of valuation subrings of $F_0$. Assume (i) for every $O \in V$ the subring $O$ is a discrete valuation ring, and (ii) every $O \in V$ admits an element $f \in F_0$ with $f \in O$ such that for every polynomial $p \in A_0[X]$ having at least one coefficient that is a unit of $A_0$, the value $\mathrm{eval}_2(j_0, f, p) = p^{j_0}(f)$ lies in $O$ and, viewed as an element of $O$, is a unit of $O$. The conclusion is that a single element works for all members of $V$ at once: there exists $f \in F_0$ such that for every $O \in V$ one has $f \in O$ and, for every $p \in A_0[X]$ with some unit coefficient, $p^{j_0}(f)$ lies in $O$ and is a unit of $O$. (Over a field with residue field of $O$, the unit condition says the residue of $f$ is transcendental over the image of $A_0$.)
--
--   This is an approximation statement of the Chinese-remainder type: finitely many pairwise incomparable discrete valuation subrings of a field, each carrying a residually transcendental element over the image of $A_0$, carry a common such element. It feeds the construction of a normal proper relative model from a finite family of valuation subrings, [`AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian`](thm.html#AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian), where the common element serves as a coordinate whose Gauss valuation all the given valuations extend.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
    {A₀ : Type} [CommRing A₀] {F₀ : Type} [Field F₀] (j₀ : A₀ →+* F₀)
    (V : Finset (ValuationSubring F₀))
    (hdvr : ∀ O ∈ V, IsDiscreteValuationRing ↥O)
    (hgeo : ∀ O ∈ V, ∃ f : F₀, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ f : F₀, ∀ O ∈ V, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O) := by sorry
