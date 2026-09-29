-- Prove2me | Theorems.Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
-- name    : ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/5769089f-79ec-52bc-ba0b-e4bc61ff9e8a
-- title:
--   Henselianity of A ∩ L^I for I inside inertia
-- statement:
--   Let $K$ and $L$ be fields in a common universe, with $L$ a $K$-algebra and $L$ algebraically closed. Let $A$ be a valuation subring of $L$, and let $I$ be a subgroup of the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$, subject to the single hypothesis $I \le A.\mathrm{inertiaSubgroupIn}\,K$, where [`ValuationSubring.inertiaSubgroupIn`](def/FLTPrelim_Ramification.html#L21) denotes the image of the inertia subgroup of $A$ (a subgroup of the decomposition subgroup of $A$ over $K$) under the inclusion of that decomposition subgroup into the full automorphism group; thus every element of $I$ stabilises $A$ and acts trivially on its residue field. The conclusion is that the subring of $L$ obtained as the infimum (intersection) of the underlying subring of $A$ and the underlying subring of the intermediate field $\mathrm{fixedField}\,I = L^{I}$, regarded as a type via its coercion, is a henselian local ring. No hypothesis is imposed on the extension $L/K$ beyond $L$ being algebraically closed, and none on residue characteristics.
--
--   This is the Henselianity of the valuation ring $A \cap L^{I}$ cut out on a fixed field of a subgroup of the inertia group of a place of an algebraically closed field; it specialises, for $I$ the full inertia subgroup, to the statement about the inertia field. It provides the base rings over which simple roots, and hence prime-to-$p$ torsion sections of curves, may be lifted, and is invoked in the reduction arguments for torsion points on the modular curve $X_1$ and in the Picard-group computations on algebraic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) := by sorry
