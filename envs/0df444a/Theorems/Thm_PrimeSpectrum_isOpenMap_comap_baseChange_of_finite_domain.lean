-- Prove2me | Theorems.Thm_PrimeSpectrum_isOpenMap_comap_baseChange_of_finite_domain
-- name    : PrimeSpectrum.isOpenMap_comap_baseChange_of_finite_domain
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T19:07:19.009982+00:00
-- url     : https://prove2.me/theorems/4a318182-9c8a-441c-a949-7885415a63b3
-- title:
--   Universal openness of finite domain extensions of a normal base
-- statement:
--   Let $A$ be a normal Noetherian integral domain and let $D$ be a commutative $A$-algebra that is an integral domain and is finite as an $A$-module. Assume that the structure homomorphism $A\to D$ is injective. For every commutative $A$-algebra $B$, the projection
--   $$
--   \operatorname{Spec}(B\otimes_A D)\longrightarrow\operatorname{Spec}B
--   $$
--   is an open map.
--
--   There is no Noetherian, finite-type, reducedness, or domain assumption on $B$; the zero ring is allowed. The finite algebra $D$ need not be normal or flat over $A$. No characteristic or separability hypothesis is imposed.
--
--   This is the finite integral-source case of the universal-openness criterion over a normal Noetherian base. It supplies the finite algebraic input for the passage to quasi-finite affine maps by principal localization and reduction to irreducible components.
--
--   **Formalization Note.** Finiteness means module finiteness. Injectivity is explicit, ensuring dominance of the unique irreducible source component. The tensor product represents the indicated affine base change.
--
--   The direct proof passes through a polynomial algebra with one variable for each element of the arbitrary base algebra. Normality of polynomial rings, going down, and finite presentation prove openness at this polynomial stage. An explicit residue-field construction lifts compatible prime ideals through a quotient pushout and proves that openness survives this quotient of the base. These steps give universal openness without a flatness assumption on the finite extension.
-- source:
--   Stacks Project, Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32, specialized to a finite dominant morphism between integral affine schemes with normal Noetherian target; normal schemes are geometrically unibranch by Lemma 28.16.2 (Tag 0BQ3), https://stacks.math.columbia.edu/tag/0BQ3. Module finiteness supplies finite type and quasi-finiteness, D being a domain gives the single source component, and injectivity A -> D gives dominance. The conclusion is restricted to affine base changes. Direct proof uses going down (Stacks Tag 00H8, https://stacks.math.columbia.edu/tag/00H8), finite-presentation openness (Tag 00I1, https://stacks.math.columbia.edu/tag/00I1), the polynomial normality coefficient argument (Tag 030A, https://stacks.math.columbia.edu/tag/030A), and an arbitrary-variable polynomial-presentation version of the base-change testing method in Tag 0F31, https://stacks.math.columbia.edu/tag/0F31.

import Mathlib
set_option autoImplicit false
open scoped TensorProduct Topology

/-- A finite domain extension of a normal Noetherian domain is universally open. -/
theorem PrimeSpectrum.isOpenMap_comap_baseChange_of_finite_domain
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (B : Type*) [CommRing B] [Algebra A B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] D))) := by sorry
