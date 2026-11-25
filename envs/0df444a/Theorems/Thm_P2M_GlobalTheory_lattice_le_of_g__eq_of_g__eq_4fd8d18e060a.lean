-- Prove2me | Theorems.Thm_P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a
-- name    : P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:36.230629+00:00
-- url     : https://prove2.me/theorems/c4d2a91d-514d-4c00-9460-49df69b218f7
-- title:
--   P2 M Global Theory lattice le of g  eq of g  eq 4fd8d18e060a: P2 M Global Theory lattice le of g  eq of g  eq 4fd8d18e060a
-- statement:
--   The P2 M Global Theory lattice le of g  eq of g  eq 4fd8d18e060a construction uses the P2 M Global Theory lattice le of g  eq of g  eq 4fd8d18e060a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L14-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory

theorem P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by sorry

alias «GlobalTheory».«lattice_le_of_g₂_eq_of_g₃_eq» := P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a
