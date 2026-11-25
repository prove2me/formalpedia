-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:12.712641+00:00
-- url     : https://prove2.me/theorems/1b4aeb27-b67d-449e-931c-25be421c107e
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Fubini preimage ball Prod fbe88fcf28b0: P2 M Ground Theory Heights  Heights Sphere Mean Fubini preimage ball Prod fbe88fcf28b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Fubini preimage ball Prod fbe88fcf28b0 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Fubini preimage ball Prod fbe88fcf28b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L49-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
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
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini

theorem P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0 {n : ℕ} (h : HermNorm n) (k : ℕ) :
    consEquiv k ⁻¹' ballProd h (k + 1) = ballH h ×ˢ ballProd h k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanFubini».«preimage_ballProd» := P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0
