-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_conj_eq_smul
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.conj_eq_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:05.714839+00:00
-- url     : https://prove2.me/theorems/1830b869-9b47-49f9-ae46-05f42aa0d963
-- title:
--   Unitary Group Mass Formula: conj eq smul
-- statement:
--   The Unitary Group Mass Formula construction uses the conj eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ModOne.lean#L35-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.ScMuExists.UnitaryGroupMassFormula.conj_eq_smul (N : Subgroup G) (hN : IsClosed (N : Set G)) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN := by sorry
