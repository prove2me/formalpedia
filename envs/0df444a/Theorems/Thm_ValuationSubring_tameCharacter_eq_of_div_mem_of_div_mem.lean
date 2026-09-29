-- Prove2me | Theorems.Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
-- name    : ValuationSubring.tameCharacter_eq_of_div_mem_of_div_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a77dd39c-284c-58e6-ad27-fc9d97c2a6ed
-- title:
--   Independence of the tame character under unit change of π
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $\pi,\pi' \in \overline{\mathbb{Q}}$ be nonzero elements whose ratio is a unit of $P$, in the sense that both $\pi'/\pi \in P$ and $\pi/\pi' \in P$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in `P.inertiaSubgroupIn ℚ`, that is, in the image under the inclusion of the decomposition subgroup of $P$ into $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ (the kernel of the action of the decomposition subgroup on the residue field of $P$). Then the two values of the tame character agree: $$\mathrm{tameCharacter}_{P,\pi'}(\sigma) = \mathrm{tameCharacter}_{P,\pi}(\sigma),$$ where for any $\varpi \in \overline{\mathbb{Q}}$ the element $\mathrm{tameCharacter}_{P,\varpi}(\sigma)$ of the residue field of the local ring $P$ is defined to be the residue of $\sigma\varpi/\varpi$ when this quotient lies in $P$, and $0$ otherwise.
--
--   This is the statement that the tame character attached to a place $P$ of $\overline{\mathbb{Q}}$ and an element $\pi$, restricted to inertia, depends on $\pi$ only through its class modulo units of $P$ — the independence-of-uniformiser property of Serre's fundamental characters of tame inertia, here in the form of an arbitrary unit ratio rather than a comparison of two uniformisers. It is used in the analysis of the restriction to inertia of the $\ell$-adic representations attached to modular forms, for instance in [`ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn`](thm.html#ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn) and [`CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two`](thm.html#CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.tameCharacter_eq_of_div_mem_of_div_mem
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by sorry
