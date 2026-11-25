-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:27.090969+00:00
-- url     : https://prove2.me/theorems/12f2a5b1-7119-49e6-89f2-246337988a4a
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm norm ne zero 0d8080cf190b: P2 M Ground Theory Heights  Heights Herm Norm norm ne zero 0d8080cf190b
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm norm ne zero 0d8080cf190b construction uses the P2 M Ground Theory Heights  Heights Herm Norm norm ne zero 0d8080cf190b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : h.norm v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«norm_ne_zero» := P2M_GroundTheory_Heights__Heights_HermNorm_norm_ne_zero_0d8080cf190b
