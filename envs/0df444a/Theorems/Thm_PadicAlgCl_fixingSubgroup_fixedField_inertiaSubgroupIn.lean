-- Prove2me | Theorems.Thm_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn
-- name    : PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c1327c91-03e1-5b13-8bf9-d2d84c20d5e5
-- title:
--   Local inertia is the fixing subgroup of its fixed field
-- statement:
--   Let $p$ be a prime and let $\mathbb{Q}_p^{\mathrm{alg}} =$ `PadicAlgCl p` be the algebraic closure of $\mathbb{Q}_p$ carried by the project, equipped with its $\mathbb{R}_{\ge 0}$-valued valuation `Valued.v`; let $A =$ [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) be the valuation subring of that valuation, i.e. the elements of valuation at most $1$. Inside the group $\mathbb{Q}_p^{\mathrm{alg}} \simeq_{\mathrm{alg}[\mathbb{Q}_p]} \mathbb{Q}_p^{\mathrm{alg}}$ of $\mathbb{Q}_p$-algebra automorphisms, let $I = A.\mathtt{inertiaSubgroupIn}\ \mathbb{Q}_p$ be the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}_p$ (the stabiliser of $A$ for the pointwise action of automorphisms on valuation subrings), of the inertia subgroup of $A$, that is of the kernel of the induced action on the residue field of $A$. The assertion is the equality of subgroups $$\mathrm{Fix}\big(\mathrm{Fixed}(I)\big) = I,$$ where $\mathrm{Fixed}(I)$ is the intermediate field of elements of $\mathbb{Q}_p^{\mathrm{alg}}$ fixed by every member of $I$, and $\mathrm{Fix}$ denotes the subgroup of automorphisms fixing that intermediate field pointwise. Equivalently: every $\mathbb{Q}_p$-automorphism fixing the inertia-fixed field pointwise already lies in $I$.
--
--   Classically, the fixed field of the inertia subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ is the maximal unramified extension $\mathbb{Q}_p^{\mathrm{nr}}$, and the statement records that inertia is recovered as the full Galois group of $\overline{\mathbb{Q}}_p$ over that field, i.e. that inertia is a closed subgroup in the Krull topology. It is used in the local analysis of Galois representations, notably by [`PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq`](thm.html#PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq) and [`PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation`](thm.html#PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn (p : ℕ) [Fact p.Prime] :
    (IntermediateField.fixedField ((padicIntegers p).inertiaSubgroupIn ℚ_[p])).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by sorry
