-- Prove2me | Theorems.Thm_P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
-- name    : P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:19.687895+00:00
-- url     : https://prove2.me/theorems/81a2f385-e539-4757-98bf-a8e6b0c16213
-- title:
--   P2 M Global Theory lattice eq of g  eq of g  eq 399c7fadf18d: P2 M Global Theory lattice eq of g  eq of g  eq 399c7fadf18d
-- statement:
--   The P2 M Global Theory lattice eq of g  eq of g  eq 399c7fadf18d construction uses the P2 M Global Theory lattice eq of g  eq of g  eq 399c7fadf18d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L40-L42

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

theorem P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by sorry

alias «GlobalTheory».«lattice_eq_of_g₂_eq_of_g₃_eq» := P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
