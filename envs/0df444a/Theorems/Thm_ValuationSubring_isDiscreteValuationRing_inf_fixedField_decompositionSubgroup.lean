-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
-- name    : ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d95b7db7-c49f-53bd-a71b-b1c493ef3055
-- title:
--   The decomposition ring of a place of ℚ̄ over ℓ
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and let $\ell$ be a prime number, and assume `A.LiesOverPrime ℓ`, i.e. that the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in the nonunits of $A$ (so $A$ is a place over $\ell$). Write $D_A =$ `A.decompositionSubgroup ℚ` for the decomposition subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, let $F$ be the fixed field of $D_A$, and let $\mathcal{O}$ be the subring of $\overline{\mathbb{Q}}$ given by the infimum of the underlying subring of $A$ and the underlying subring of $F$, that is $\mathcal{O} = A \cap F$. The conclusion is a conjunction of three assertions: $\mathcal{O}$ is a discrete valuation ring; the image of the natural number $\ell$ in $\mathcal{O}$ is irreducible, so that $\ell$ is a uniformiser; and every $x \in \mathcal{O}$ whose image in $\overline{\mathbb{Q}}$ has $A$-valuation strictly less than $1$ fails to be a unit of $\mathcal{O}$, i.e. the maximal ideal of $\mathcal{O}$ contains $\mathfrak{m}_A \cap \mathcal{O}$.
--
--   Classically this records that the decomposition field $F$ of a place $A$ of $\overline{\mathbb{Q}}$ above $\ell$ is unramified with residue degree one over $\mathbb{Q}$ at $\ell$, so that $A \cap F$ is a discrete valuation ring with uniformiser $\ell$ and with maximal ideal induced by that of $A$. It supplies the base discrete valuation ring over which the finite flat group schemes and $p$-divisible groups of the multiplicative-type and ordinarity arguments are considered; the proof cites [`ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup`](thm.html#ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    IsDiscreteValuationRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      Irreducible ((ℓ : ℕ) : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring)) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x := by sorry
