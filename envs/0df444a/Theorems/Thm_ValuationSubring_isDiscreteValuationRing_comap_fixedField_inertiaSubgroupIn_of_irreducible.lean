-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
-- name    : ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/ea9e2a44-b07a-51ab-8df8-3596a8a97700
-- title:
--   Inertia ring over a number field is an unramified DVR
-- statement:
--   Let $F$ be a number field equipped with an embedding into $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, let $P$ be a valuation subring of $\overline{\mathbb Q}$, and let $q$ be a prime number such that $P$ lies over $q$ in the sense that the image of $q$ in $\overline{\mathbb Q}$ is a non-unit of $P$. Let $\varpi \in F$ be an element whose image in $\overline{\mathbb Q}$ lies in $P$ and which, regarded as an element of the valuation subring $P \cap F$ of $F$ (the preimage of $P$ under $F \to \overline{\mathbb Q}$), is irreducible. Write $I$ for `P.inertiaSubgroupIn F`, the image in $\overline{\mathbb Q} \simeq_{\mathrm{alg}[F]} \overline{\mathbb Q}$ of the inertia subgroup of $P$ over $F$ under the inclusion of the decomposition subgroup, and let $T = \overline{\mathbb Q}^{I}$ be its fixed field, an intermediate field of $\overline{\mathbb Q}/F$. The conclusion is fourfold: the valuation subring $P \cap T$ (the preimage of $P$ under $T \to \overline{\mathbb Q}$) is a discrete valuation ring; the element $\varpi$, viewed in $P \cap T$ via $F \subseteq T$, is irreducible there; $P \cap T$ has characteristic zero; and every $y \in P$ fixed by every $\sigma \in I$ is the image of an element of $P \cap T$.
--
--   This is the statement that the inertia field $T$ of a place $P$ of $\overline{\mathbb Q}$ over a number field $F$ is unramified over $F$: a uniformiser $\varpi$ of $P \cap F$ remains a uniformiser of the discrete valuation ring $P \cap T$, which is exactly the ring of $I$-fixed elements of $P$. It is the number-field-base form of the corresponding statement over $\mathbb Q$, and is used in the construction of valuation subrings with admissible constants over a cyclotomic field, where the base must be allowed to contain a ramified cyclotomic extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))))) :
    IsDiscreteValuationRing
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      Irreducible ((⟨⟨algebraMap F (AlgebraicClosure ℚ) ϖ, IntermediateField.algebraMap_mem _ ϖ⟩, hϖP⟩ :
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))))) ∧
      CharZero
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))) ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn F, σ y = y) →
        ∃ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ))),
          ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F))) : AlgebraicClosure ℚ) = y := by sorry
