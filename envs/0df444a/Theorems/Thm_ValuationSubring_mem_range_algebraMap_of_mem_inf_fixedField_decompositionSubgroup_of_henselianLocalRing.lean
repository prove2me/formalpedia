-- Prove2me | Theorems.Thm_ValuationSubring_mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing
-- name    : ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/ab2d7918-730f-57cd-9b05-3d7d6625a4d4
-- title:
--   Decomposition ring of a place of ℚ̄ maps into any henselian dominating local domain
-- statement:
--   Fix a prime $p$ and a valuation subring $Pl$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ satisfying `Pl.LiesOverPrime p`, i.e. the image of $p$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ lies in `Pl.nonunits` (it belongs to $Pl$ and is not a unit there). Let $Rh$ be a commutative ring which is a domain and a henselian local ring, equipped with an algebra structure over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ whose structure map is injective (the `FaithfulSMul` hypothesis), and assume: every element of $Rh$ has its image under `algebraMap Rh (AlgebraicClosure ℚ)` in $Pl$; and an element of $Rh$ lies in the maximal ideal `maximalIdeal Rh` if and only if the $Pl$-valuation of its image is $<1$, so that the structure map is local for the valuation. The conclusion asserts that every $x$ in the intersection, inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, of the subring underlying $Pl$ with the subring underlying the fixed field of the decomposition subgroup `Pl.decompositionSubgroup ℚ` lies in the range of `algebraMap Rh (AlgebraicClosure ℚ)`.
--
--   The intersection of $Pl$ with the fixed field of its decomposition group is the henselisation of $\mathbb{Z}_{(p)}$ realised inside $\bar{\mathbb{Q}}$, and the statement expresses its universal property in the concrete form needed later: it maps into any henselian local domain dominated by the place. It is used in the construction of $p$-divisible groups and retractions attached to Néron models of modular curves at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.mem_range_algebraMap_of_mem_inf_fixedField_decompositionSubgroup_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1) :
    ∀ x : AlgebraicClosure ℚ, x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring →
      x ∈ Set.range (algebraMap Rh (AlgebraicClosure ℚ)) := by sorry
