-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4
-- name    : P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:15.506149+00:00
-- url     : https://prove2.me/theorems/458c9a17-f8ad-461f-9d23-61fd99f332d9
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean Fubini cons Equiv apply f1f52a18dac4: P2 M Ground Theory Heights  Heights Sphere Mean Fubini cons Equiv apply f1f52a18dac4
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean Fubini cons Equiv apply f1f52a18dac4 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean Fubini cons Equiv apply f1f52a18dac4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSphereMeanFubini.lean#L26-L41

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

theorem P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4 {n k : ℕ} (p : (Fin n → ℂ) × (Fin k × Fin n → ℂ)) :
    consEquiv k p = consGroup p.1 p.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMeanFubini».«consEquiv_apply» := P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4
