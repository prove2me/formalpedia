-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant
-- name    : ValuationSubring.exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0a5da316-7b22-53f1-bec0-f92c80e218b1
-- title:
--   Residual transcendence descends to an algebraic subfield
-- statement:
--   Let $F$ be a field, $F_0 \subseteq F$ a subfield such that every element of $F$ is algebraic over $F_0$, and $O$ a valuation subring of $F$. Let $A_0$ be a commutative local ring with a ring homomorphism $j : A_0 \to F_0$ whose image lies in $O$, such that $j$ carries the maximal ideal of $A_0$ into the maximal ideal of $O$, and such that for every monic polynomial $p$ over $A_0$ of positive degree there is $a \in A_0$ with $j(p(a))$ in the maximal ideal of $O$ (a residual algebraic closedness condition). Let $A$ be a subring of $F$ contained in $O$ and containing the image of $j$, every element of which is congruent modulo the maximal ideal of $O$ to the image under $j$ of an element of $A_0$. Finally let $t \in O$ be such that $t - a$ is a unit of $O$ for every $a \in A$. Then there exists $f \in F_0$ lying in the valuation subring $O \cap F_0$ of $F_0$ (the comap of $O$ along the inclusion of $F_0$) such that for every polynomial $p$ over $A_0$ having at least one unit coefficient, the value $\mathrm{eval}_2\,j\,f\,p$ lies in $O \cap F_0$ and is a unit there.
--
--   This is the descent of residually transcendental (type II) valuations along an algebraic extension of fields: a residually non-constant element of $O$ forces the trace $O \cap F_0$ to contain an element that is residually transcendental over the constants $A_0$, in the strong form that every unit-coefficient polynomial expression in it is a unit. It supplies the geometricity input for the three statements producing semistable models of the full-level modular curve from given valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_isUnit_polynomialEval2_comap_of_residuallyNonconstant
    {F : Type} [Field F] (F₀ : Subfield F)
    (halg : ∀ x : F, IsAlgebraic ↥F₀ x)
    (O : ValuationSubring F)
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀]
    (j : A₀ →+* ↥F₀) (hjO : ∀ a : A₀, ((j a : ↥F₀) : F) ∈ O)

    (hloc : ∀ a : A₀, a ∈ maximalIdeal A₀ → ∃ h : ((j a : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)
    (hac : ∀ p : Polynomial A₀, p.Monic → 0 < p.natDegree →
      ∃ a : A₀, ∃ h : ((j (p.eval a) : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)

    (A : Subring F) (hAO : ∀ a : F, a ∈ A → a ∈ O) (hjA : ∀ a₀ : A₀, ((j a₀ : ↥F₀) : F) ∈ A)
    (hres : ∀ a : F, a ∈ A → ∃ a₀ : A₀, ∃ h : a - ((j a₀ : ↥F₀) : F) ∈ O, (⟨_, h⟩ : ↥O) ∈ maximalIdeal ↥O)

    (t : F) (ht : t ∈ O) (htu : ∀ a : F, a ∈ A → ∃ h : t - a ∈ O, IsUnit (⟨_, h⟩ : ↥O)) :
    ∃ f : ↥F₀, f ∈ O.comap F₀.subtype ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j f p ∈ O.comap F₀.subtype, IsUnit (⟨_, hO⟩ : ↥(O.comap F₀.subtype)) := by sorry
