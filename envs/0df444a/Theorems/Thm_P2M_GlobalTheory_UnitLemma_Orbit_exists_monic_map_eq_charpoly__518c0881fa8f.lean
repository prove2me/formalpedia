-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f
-- name    : P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:24.255907+00:00
-- url     : https://prove2.me/theorems/70456d55-f2a4-4ef9-9cf6-ad1a89ca5960
-- title:
--   P2 M Global Theory Unit Lemma Orbit exists monic map eq charpoly  518c0881fa8f: P2 M Global Theory Unit Lemma Orbit exists monic map eq charpoly  518c0881fa8f
-- statement:
--   The P2 M Global Theory Unit Lemma Orbit exists monic map eq charpoly  518c0881fa8f construction uses the P2 M Global Theory Unit Lemma Orbit exists monic map eq charpoly  518c0881fa8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L95-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}

theorem P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f (B : InvAlg K) (hs : B.P.Separable) (hi : IsIntegral K.O B.g) :
    ∃ p : K.O[X], p.Monic ∧ p.map (algebraMap K.O K.E) = B.P := by sorry

alias «GlobalTheory».«UnitLemma».«Orbit».«exists_monic_map_eq_charpoly₂» := P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f
