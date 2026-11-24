-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98
-- name    : P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:19.477271+00:00
-- url     : https://prove2.me/theorems/9481e93a-0f14-485b-bfc6-0069c7ad2784
-- title:
--   P2 M Ground Theory Heights  Heights norm le of herm Norm lt 7188355ead98: P2 M Ground Theory Heights  Heights norm le of herm Norm lt 7188355ead98
-- statement:
--   The P2 M Ground Theory Heights  Heights norm le of herm Norm lt 7188355ead98 construction uses the P2 M Ground Theory Heights  Heights norm le of herm Norm lt 7188355ead98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L43-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98 (h : HermNorm n) {v : Fin n → ℂ} (hv : h.norm v < 1) (j : Fin n) :
    ‖v j‖ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«norm_le_of_hermNorm_lt» := P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98
