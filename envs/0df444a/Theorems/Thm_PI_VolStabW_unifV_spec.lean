-- Prove2me | Theorems.Thm_PI_VolStabW_unifV_spec
-- name    : PI.VolStabW.unifV_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:38.321865+00:00
-- url     : https://prove2.me/theorems/13e222d7-4e5c-4f35-b564-e1e74ab84d8d
-- title:
--   Vol Stab W: unif V spec
-- statement:
--   The Vol Stab W construction uses the unif V spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnifVSpec.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnifVSpec.lean#L20-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensAAOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem PI.VolStabW.unifV_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    unifV v ≠ 0 ∧ Tendsto (fun k : ℕ => unifV v ^ k) atTop (𝓝 0) ∧
      unifV v ∈ v.adicCompletionIntegers F := by sorry
