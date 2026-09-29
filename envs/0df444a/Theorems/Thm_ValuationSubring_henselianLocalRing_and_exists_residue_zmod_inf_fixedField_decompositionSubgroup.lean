-- Prove2me | Theorems.Thm_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
-- name    : ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b90ae392-a745-542f-8d1b-4425d3094cc9
-- title:
--   The decomposition ring of a place of ℚ̄ over ℓ
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $\ell$ be a prime number, and assume `A.LiesOverPrime ℓ`, which by definition says that the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits`, i.e. has $A$-valuation less than $1$. Write $D_A =$ `A.decompositionSubgroup ℚ` for the decomposition subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, let $Z$ be the fixed field `IntermediateField.fixedField` of $D_A$, and let $O$ be the subring of $\overline{\mathbb{Q}}$ obtained as the infimum (intersection) of the underlying subrings of $A$ and of $Z$. The conclusion is threefold: first, $O$ is a Henselian local ring; second, there is a ring homomorphism $\pi : O \to \mathbb{Z}/\ell$ which is surjective and whose kernel is exactly the set of $x \in O$ with $A$-valuation of $x$ (as an element of $\overline{\mathbb{Q}}$) strictly less than $1$; third, for every $x \in O$, $x$ fails to be a unit of $O$ if and only if the $A$-valuation of $x$ is strictly less than $1$. Together the last two clauses identify the maximal ideal of $O$ with $\{x : v_A(x) < 1\}$ and the residue field of $O$ with $\mathbb{F}_\ell$.
--
--   This is the classical statement that the decomposition ring $A \cap \overline{\mathbb{Q}}^{D_A}$ at a place of $\overline{\mathbb{Q}}$ above $\ell$ is henselian with residue field $\mathbb{F}_\ell$, the maximal ideal being cut out by the valuation; a companion statement records that this ring is in addition a discrete valuation ring with uniformiser $\ell$. It serves as the source of the Henselian local base ring, together with its reduction map to $\mathbb{Z}/\ell$, used in the Čerednik–Drinfeld and modular-curve arguments on finite parts, $p$-divisible groups and Tate modules that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    HenselianLocalRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      (∃ π : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) →+* ZMod ℓ,
        Function.Surjective π ∧
        ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
          π x = 0 ↔ A.valuation (x : AlgebraicClosure ℚ) < 1) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        ¬ IsUnit x ↔ A.valuation (x : AlgebraicClosure ℚ) < 1 := by sorry
