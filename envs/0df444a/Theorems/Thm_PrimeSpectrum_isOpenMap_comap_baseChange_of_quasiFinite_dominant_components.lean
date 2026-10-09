-- Prove2me | Theorems.Thm_PrimeSpectrum_isOpenMap_comap_baseChange_of_quasiFinite_dominant_components
-- name    : PrimeSpectrum.isOpenMap_comap_baseChange_of_quasiFinite_dominant_components
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T18:21:44.852085+00:00
-- url     : https://prove2.me/theorems/483b3953-473a-4709-acb3-0dd722ab9734
-- title:
--   Universal openness of quasi-finite algebras with dominating components
-- statement:
--   Let $A$ be a normal Noetherian integral domain, and let $R$ be a finite-type quasi-finite commutative $A$-algebra. Assume that every irreducible component $Z$ of $\operatorname{Spec}R$ dominates $\operatorname{Spec}A$:
--   $$
--   \overline{f(Z)}=\operatorname{Spec}A,
--   \qquad
--   f:\operatorname{Spec}R\longrightarrow\operatorname{Spec}A.
--   $$
--   For every commutative $A$-algebra $B$, the projection
--   $$
--   \operatorname{Spec}(B\otimes_A R)\longrightarrow\operatorname{Spec}B
--   $$
--   is open.
--
--   The algebra $B$ is arbitrary: it need not be Noetherian, reduced, or of finite type. The algebra $R$ need not be reduced, and its structure map is not assumed flat. The zero ring is allowed for $R$ or $B$, with the usual empty-spectrum conventions.
--
--   This is the affine normal-base specialization of the universal-openness criterion for locally quasi-finite morphisms with dominating components. It is the geometric input for passing from individual open affine families to their finite products.
--
--   **Formalization Note.** Dominance is density of the image in the Zariski topology. Normality is expressed by the domain and integral-closedness assumptions on $A$. Finite type is separate from Mathlib's quasi-finiteness class, which records finite-dimensional residue-field fibers. Only affine base changes are stated, as required by the tensor-product application.
--
--   **Verified reduction (8 October 2026).** Openness after arbitrary affine base change is reduced to the [finite injective domain-extension case](https://prove2.me/theorems/4a318182-9c8a-441c-a949-7885415a63b3). The reduction proves point lifting through tensor products with component quotients, derives injectivity of each component's structure map from dominance, and applies the algebraic Zariski main theorem to finite subalgebra models on principal neighborhoods. Tensor-localization compatibility and the open-neighborhood assembly are proved. The finite-extension child remains Open; the original formal statement is unchanged.
-- source:
--   Stacks Project, Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32, and Lemma 28.16.2 (Tag 0BQ3), https://stacks.math.columbia.edu/tag/0BQ3. This is the affine specialization to a normal Noetherian integral base: normal schemes are geometrically unibranch, and finite type together with finite-dimensional residue-field fibers gives local quasi-finiteness. The stated component-dominance hypothesis is the source hypothesis. Universal openness in 0F32 gives the conclusion for every affine base change Spec B -> Spec A; the fiber product is Spec(B tensor_A R). This single-morphism geometric criterion remains Open.

import Mathlib
set_option autoImplicit false
open scoped TensorProduct Topology

/-- The normal-base quasi-finite universal-openness criterion in affine form. -/
theorem PrimeSpectrum.isOpenMap_comap_baseChange_of_quasiFinite_dominant_components
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (R : Type*) [CommRing R] [Algebra A R]
    [Algebra.FiniteType A R] [Algebra.QuasiFinite A R]
    (hdom : ∀ Z ∈ irreducibleComponents (PrimeSpectrum R),
      Dense (PrimeSpectrum.comap (algebraMap A R) '' Z))
    (B : Type*) [CommRing B] [Algebra A B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] R))) := by sorry
