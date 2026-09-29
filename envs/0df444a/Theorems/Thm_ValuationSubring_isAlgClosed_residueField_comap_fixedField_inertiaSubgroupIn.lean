-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
-- name    : ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/0fca54f4-ab59-500d-b3b9-6ff756bd91bf
-- title:
--   Residue field of the inertia ring of a place of ℚ̄ is algebraically closed
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` and let $q$ be a prime natural number such that $P$ satisfies `LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb Q}$ lies in the set of non-units of $P$. Let $F$ be a field equipped with an algebra structure over $\overline{\mathbb Q}$, so that $\overline{\mathbb Q}$ is an extension of $F$. Write $I_F =$ `P.inertiaSubgroupIn F` for the subgroup of $\overline{\mathbb Q} \simeq_{\text{alg}[F]} \overline{\mathbb Q}$ obtained as the image of the inertia subgroup of $P$ over $F$ under the inclusion of the decomposition subgroup of $P$ over $F$, and let $K_0 = \overline{\mathbb Q}^{I_F}$ be the corresponding fixed intermediate field. The assertion is that the residue field of the valuation subring $P \cap K_0$ of $K_0$ — formally, the preimage `P.comap` of $P$ along the structure map $K_0 \to \overline{\mathbb Q}$ — is algebraically closed.
--
--   Classically this expresses that the inertia field of a place of $\overline{\mathbb Q}$ over $q$ is its own maximal unramified subextension, with residue field the whole of $\overline{\mathbb F}_q$; the inclusion $P \cap K_0 \hookrightarrow P$ induces an isomorphism of residue fields. It supplies algebraically closed residue fields for the local study of models of modular curves, and is used in the construction of valuation subrings with admissible constants over cyclotomic fields and in the local analysis of Néron objects and of torsion in differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (F : Type) [Field F] [Algebra F (AlgebraicClosure ℚ)] :
    IsAlgClosed (IsLocalRing.ResidueField
      ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn F)) (AlgebraicClosure ℚ)))) := by sorry
