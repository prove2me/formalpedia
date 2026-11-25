-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AdmissibleAE_formsIn_ne_top_cb95a9d30a4b
-- name    : P2M_GroundTheory_Heights__Heights_AdmissibleAE_formsIn_ne_top_cb95a9d30a4b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:54.352318+00:00
-- url     : https://prove2.me/theorems/d270d7e0-3961-4ab0-8513-6f6460ac97a7
-- title:
--   P2 M Ground Theory Heights  Heights Admissible AE forms In ne top cb95a9d30a4b: P2 M Ground Theory Heights  Heights Admissible AE forms In ne top cb95a9d30a4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Admissible AE forms In ne top cb95a9d30a4b construction uses the P2 M Ground Theory Heights  Heights Admissible AE forms In ne top cb95a9d30a4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAE.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAE.lean#L35-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAE
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
open MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.AdmissibleAE
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AdmissibleAE_formsIn_ne_top_cb95a9d30a4b {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsRelevant W) : formsIn W ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AdmissibleAE».«formsIn_ne_top» := P2M_GroundTheory_Heights__Heights_AdmissibleAE_formsIn_ne_top_cb95a9d30a4b
