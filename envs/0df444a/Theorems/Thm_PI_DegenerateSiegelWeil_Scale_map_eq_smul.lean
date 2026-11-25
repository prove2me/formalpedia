-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_map_eq_smul
-- name    : PI.DegenerateSiegelWeil.Scale.map_eq_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:35.178824+00:00
-- url     : https://prove2.me/theorems/8578fca1-d7f9-584d-a3cc-3742a6ef5bed
-- title:
--   Scale: map eq smul
-- statement:
--   The Scale construction uses the map eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/AddEquivAddHaarCharEqOne.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/AddEquivAddHaarCharEqOne.lean#L65-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem PI.DegenerateSiegelWeil.Scale.map_eq_smul (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ G) :
    μ.map e = (((addEquivAddHaarChar e)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by sorry
