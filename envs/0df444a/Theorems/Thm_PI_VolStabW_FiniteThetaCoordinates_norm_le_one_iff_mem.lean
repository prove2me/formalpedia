-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_norm_le_one_iff_mem
-- name    : PI.VolStabW.FiniteThetaCoordinates.norm_le_one_iff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:09.976391+00:00
-- url     : https://prove2.me/theorems/25df7409-6cc6-4ed6-b5bf-877ce8286183
-- title:
--   Finite Theta Coordinates: norm le one iff mem
-- statement:
--   The Finite Theta Coordinates construction uses the norm le one iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L149-L152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]

theorem PI.VolStabW.FiniteThetaCoordinates.norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    ‖x‖ ≤ 1 ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v := by sorry
