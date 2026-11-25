-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d
-- name    : P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:52.01348+00:00
-- url     : https://prove2.me/theorems/33805c33-36d3-5322-ba68-1344f7faeb7e
-- title:
--   P2 M Ground Theory Heights  Heights Is Admissible nrmv 70a1134c823d: P2 M Ground Theory Heights  Heights Is Admissible nrmv 70a1134c823d
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Admissible nrmv 70a1134c823d construction uses the P2 M Ground Theory Heights  Heights Is Admissible nrmv 70a1134c823d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAENrm.lean#L29-L44

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

theorem P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d (h : HermNorm n) {Z : ProjCycle ℂ n} {v : Fin n → ℂ}
    (hv : IsAdmissible Z v) : IsAdmissible Z (nrmv h v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsAdmissible».«nrmv» := P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d
