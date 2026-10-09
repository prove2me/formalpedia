-- Prove2me | Theorems.Thm_PiTensorProduct_isOpenMap_comap_of_quasiFinite
-- name    : PiTensorProduct.isOpenMap_comap_of_quasiFinite
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T17:29:35.498127+00:00
-- url     : https://prove2.me/theorems/12366d22-835f-4ccc-9f99-abe1ff4a5d03
-- title:
--   Openness of finite tensor products over a normal Noetherian domain
-- statement:
--   Let $A$ be a normal Noetherian integral domain, let $I$ be a finite set, and let $R_i$ be a finite-type commutative $A$-algebra for each $i\in I$. Suppose each structure morphism
--   $$
--   f_i:\operatorname{Spec}R_i\longrightarrow\operatorname{Spec}A
--   $$
--   is open and quasi-finite. Then the structure morphism
--   $$
--   \operatorname{Spec}\!\left(\bigotimes_{i\in I,A} R_i\right)
--   \longrightarrow\operatorname{Spec}A
--   $$
--   is open.
--
--   No reducedness, flatness or surjectivity is assumed for the $R_i$. For an empty index set the tensor product is $A$, and the conclusion is the openness of the identity. The zero ring is allowed among the $R_i$.
--
--   This isolates the geometric input needed to specialize finitely many rational points subject to a joint polynomial nonvanishing condition. It is an affine finite-product consequence of universal openness over a geometrically unibranch base, rather than a verbatim statement of the cited source lemma.
--
--   **Formalization Note.** Finite type is separate from Mathlib's Algebra.QuasiFinite, which asserts finite-dimensional residue-field fibers. Normality is expressed by IsDomain A and IsIntegrallyClosed A. The tensor product is Mathlib's PiTensorProduct; the conclusion concerns the actual Zariski topologies on prime spectra.
--
--   **Verified reduction (8 October 2026).** Component dominance is now proved from ordinary openness and Noetherianity. The full finite-family assembly is also proved: the empty tensor product, reindexing and one-factor splitting are verified as algebra isomorphisms, and induction composes the appropriate affine base-change maps. The sole Open input is [the single-algebra normal-base universal-openness criterion with dominating components](https://prove2.me/theorems/483b3953-473a-4709-acb3-0dd722ab9734), an affine specialization of Stacks Tag 0F32. The original formal statement is unchanged.
-- source:
--   Stacks Project, Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32; Lemma 28.16.2 (Tag 0BQ3), https://stacks.math.columbia.edu/tag/0BQ3; Definition 29.24.1 and Lemma 29.24.3 (Section Tag 01TZ), https://stacks.math.columbia.edu/tag/01TZ. Auxiliary affine finite-product consequence: finite-type sources over the Noetherian base have finitely many irreducible components. A nonempty open part belonging to only one component has nonempty open image, so every component dominates the integral base. Normality makes the base geometrically unibranch; 0F32 gives universal openness of each quasi-finite map. Base change and composition yield openness of their finite fiber product. These geometric steps remain Open in the formalization.

import Mathlib
set_option autoImplicit false
open scoped TensorProduct Topology

/-- Finite tensor products of open quasi-finite affine families are open over
a normal Noetherian domain. -/
theorem PiTensorProduct.isOpenMap_comap_of_quasiFinite
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (ι : Type*) [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.FiniteType A (R i)]
    (hopen : ∀ i, IsOpenMap (PrimeSpectrum.comap (algebraMap A (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite A (R i)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (⨂[A] i, R i))) := by sorry
