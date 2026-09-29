-- Prove2me | Theorems.Thm_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
-- name    : Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/fb6f4407-6882-5214-a0cc-164d3c984d09
-- title:
--   Fraction subring of a field is the localisation at P
-- statement:
--   Let $A$ be a commutative ring, $K$ a field with an $A$-algebra structure, $R$ an $A$-subalgebra of $K$, $P$ a maximal ideal of $R$, and $O$ a subring of $K$ such that for all $f \in K$ one has $f \in O$ if and only if there exist $g, h \in R$ with $h \notin P$ and $f h = g$ in $K$. The conclusion asserts, first, that every element of $R$ lies in $O$ (giving the inclusion proof $hRO$), and second, that there is a ring isomorphism $e$ from the localisation $\mathrm{Localization.AtPrime}\ P$ onto $O$ carrying the image of each $r \in R$ under the structure map to $r$ viewed in $O$. It further asserts that $O$ is a local ring, and for that local structure: an element $f \in O$ lies in the maximal ideal of $O$ exactly when $f h = g$ for some $g \in P$ and $h \in R \setminus P$; for $r \in R$, the element $r$ of $O$ lies in the maximal ideal exactly when $r \in P$; if $R$ is a Noetherian ring then so is $O$; and if every $r \in R$ satisfies $r - a \in P$ for some $a$ in the image of $A \to R$, then for every $f \in O$ there is $a \in A$ whose image lies in $O$ with $f - a$ a non-unit of $O$.
--
--   This is the dictionary between the description of the local ring of an affine chart at a closed point as a subring of fractions inside the function field and the abstract localisation at a prime, together with the standard consequences (locality, the shape of the maximal ideal, transfer of Noetherianity, and surjectivity of $A$ onto the residue field in the form 'every element of $O$ differs from an element of $A$ by a non-unit'). It is used to identify the local rings at the ends of blown-up charts of modular curves, which are specified by exactly this fraction condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
    {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K]
    (R : Subalgebra A K) (P : Ideal ↥R) (hP : P.IsMaximal) (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥R, h ∉ P ∧ f * (h : K) = (g : K)) :
    ∃ (hRO : ∀ r : ↥R, (r : K) ∈ O)
      (e : Localization.AtPrime P ≃+* ↥O),
      (∀ r : ↥R, e (algebraMap ↥R (Localization.AtPrime P) r) = ⟨(r : K), hRO r⟩) ∧
      ∃ _ : IsLocalRing ↥O,
        (∀ (f : K) (hf : f ∈ O), (⟨f, hf⟩ : ↥O) ∈ maximalIdeal ↥O ↔
            ∃ g h : ↥R, g ∈ P ∧ h ∉ P ∧ f * (h : K) = (g : K)) ∧
        (∀ r : ↥R, (⟨(r : K), hRO r⟩ : ↥O) ∈ maximalIdeal ↥O ↔ r ∈ P) ∧
        (IsNoetherianRing ↥R → IsNoetherianRing ↥O) ∧
        ((∀ r : ↥R, ∃ a : A, r - algebraMap A ↥R a ∈ P) →
          ∀ (f : K) (hf : f ∈ O), ∃ (a : A) (ha : algebraMap A K a ∈ O),
            ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨algebraMap A K a, ha⟩)) := by sorry
