-- Prove2me | Theorems.Thm_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
-- name    : ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/2b2f355f-0408-5519-b846-c0488b050be5
-- title:
--   Finite henselian levels inside a valuation subring
-- statement:
--   Let $L$ be an algebraically closed field and $A$ a valuation subring of $L$. Let $A_0$ be a noetherian henselian local domain of Krull dimension at most $1$ (`Ring.KrullDimLE 1`), let $\iota : A_0 \to A$ be an injective local ring homomorphism, and let $K_0$ be a subfield of $L$ such that the image of $A_0$ in $L$ under $\iota$ is exactly $A \cap K_0$, such that $L$ is algebraic over $K_0$, and such that the composite $A_0 \to A \to A/\mathfrak{m}_A$ with the residue map of $A$ is surjective. Then for every finite subset $\Lambda$ of $L$ there is an intermediate field $K_1$ of $L/K_0$, finite-dimensional over $K_0$, with $\Lambda \subseteq K_1$, such that the valuation subring $A_1 :=$ `A.comap (algebraMap K₁ L)` of $K_1$ is noetherian and henselian local, and there are local ring homomorphisms $j : A_0 \to A_1$ and $\iota_1 : A_1 \to A$ with $\iota_1$ injective, $\iota_1 \circ j = \iota$, the composite of $\iota_1$ with the residue map of $A$ surjective, and $\iota_1$ compatible with the inclusion of $K_1$ into $L$, i.e. the image in $L$ of $\iota_1(x)$ is the image of $x \in K_1$ for all $x \in A_1$; moreover, if $A \neq L$ then $A_1$ is a discrete valuation ring. Injectivity of $j$, and a dimension bound on $A_1$, are not part of the conclusion.
--
--   This is the step that replaces a given "level" $A_0 = A \cap K_0$ of a valuation subring of an algebraically closed field by a level over a finite extension $K_1/K_0$ capturing any prescribed finite set of elements, while preserving noetherianity, henselianity, the residue field, and (in the non-trivial case) discreteness of the valuation. It is used in the study of semistable models and descent for algebraic curves, in [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent) and [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (A₀ : Type u) [CommRing A₀] [IsNoetherianRing A₀] [HenselianLocalRing A₀] [IsDomain A₀]
    (hdim : Ring.KrullDimLE 1 A₀)
    (ι : A₀ →+* A) [IsLocalHom ι] (hι : Function.Injective ι)
    (K₀ : Subfield L)
    (hrange : Set.range (fun a : A₀ => ((ι a : A) : L)) = (A : Set L) ∩ (K₀ : Set L))
    [Algebra.IsAlgebraic K₀ L]
    (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (Λ : Finset L) :
    ∃ (K₁ : IntermediateField K₀ L) (_ : FiniteDimensional K₀ K₁),
      (↑Λ : Set L) ⊆ (K₁ : Set L) ∧
      ∃ (_ : IsNoetherianRing ↥(A.comap (algebraMap K₁ L)))
        (_ : HenselianLocalRing ↥(A.comap (algebraMap K₁ L)))
        (j : A₀ →+* ↥(A.comap (algebraMap K₁ L))) (ι₁ : ↥(A.comap (algebraMap K₁ L)) →+* A)
        (_ : IsLocalHom j) (_ : IsLocalHom ι₁),
        Function.Injective ι₁ ∧ ι₁.comp j = ι ∧
        Function.Surjective ((IsLocalRing.residue A).comp ι₁) ∧
        (∀ x : ↥(A.comap (algebraMap K₁ L)), ((ι₁ x : A) : L) = algebraMap K₁ L (x : K₁)) ∧
        (A ≠ ⊤ → IsDiscreteValuationRing ↥(A.comap (algebraMap K₁ L))) := by sorry
