-- Prove2me | Theorems.Thm_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
-- name    : ValuationSubring.surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/24fbe1fe-de73-5e6c-8faa-267ba53c02a9
-- title:
--   Reduction P∩ℚ̄^I→κ(P) is surjective; unit criterion
-- statement:
--   Fix a prime number $p$ and a valuation subring $Pl$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ lies in the non-units of $Pl$. Let $I$ be a subgroup of the group of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$ contained in `Pl.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of $Pl$ under the inclusion of the decomposition subgroup. Write $O_I$ for the subring $Pl \cap \overline{\mathbb Q}^{I}$, the infimum of the underlying subring of $Pl$ and of the subring underlying the fixed field of $I$, and let $\mathrm{to}\kappa \colon O_I \to \kappa(Pl)$ be the composite of the inclusion $O_I \hookrightarrow Pl$ with the residue map of the local ring $Pl$ onto its residue field. The assertion is twofold: $\mathrm{to}\kappa$ is surjective, and for every $x \in O_I$ one has that $x$ is a unit of $O_I$ if and only if $\mathrm{to}\kappa(x) \neq 0$.
--
--   This is the standard statement that, for a place $P$ of $\overline{\mathbb Q}$ above $p$ and a subgroup $I$ of the inertia group at $P$, the ring $P \cap \overline{\mathbb Q}^{I}$ is local with residue field all of $\kappa(P)$, reduction being surjective and detecting units; in particular the residue field of $O_I$ is the algebraically closed field $\kappa(P)$. It is used in the construction of reductions of torsion points on the modular curve $X_1$, via [`ModularCurve.XOneP.exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_reduction_torsion_bijective_points_fixedValuationSubring_of_representsRelSubPic_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ) :
    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)
    Function.Surjective toκ ∧ ∀ x : ↥OI, IsUnit x ↔ toκ x ≠ 0 := by sorry
