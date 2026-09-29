-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
-- name    : ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7554f078-45a1-5c56-8fc9-f2972a628202
-- title:
--   Inertia-fixed part of a place above ℓ is a DVR with uniformiser ℓ
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and let $\ell$ be a prime number such that $P$ lies over $\ell$, i.e. the image of $\ell$ in $\overline{\mathbb{Q}}$ is a nonunit of $P$. Write $I$ for `P.inertiaSubgroupIn ℚ`, the subgroup of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $P$, let $F' = \mathrm{fixedField}(I)$ be the corresponding intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, and let $R'$ be the pullback of $P$ along the structure map $F' \to \overline{\mathbb{Q}}$, a valuation subring of $F'$. The theorem asserts four things simultaneously: $R'$ is a discrete valuation ring; the image of $\ell$ in $R'$ is irreducible; $R'$ has characteristic zero; and every $y \in P$ that is fixed by every $\sigma \in I$ is the image of some $x \in R'$ under the inclusions $R' \subseteq F' \subseteq \overline{\mathbb{Q}}$ (so that the $I$-fixed part of $P$ is exactly $R'$).
--
--   This identifies the valuation ring of the maximal unramified subextension at a place $P$ of $\overline{\mathbb{Q}}$ above $\ell$: the inertia ring $P \cap \overline{\mathbb{Q}}^{\,I_P}$ is a characteristic-zero discrete valuation ring in which $\ell$ itself is a uniformiser. It supplies the base discrete valuation ring used in the local study at $\ell$ of finite flat group schemes and of Néron models of modular curves elsewhere in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hP : P.LiesOverPrime ℓ) :
    IsDiscreteValuationRing
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
      Irreducible ((ℓ : ℕ) :
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∧
      CharZero
        ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
      ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
        ∃ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
          ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) = y := by sorry
