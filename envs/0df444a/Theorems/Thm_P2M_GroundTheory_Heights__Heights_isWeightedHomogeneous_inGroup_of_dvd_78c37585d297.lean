-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297
-- name    : P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:16.255713+00:00
-- url     : https://prove2.me/theorems/45d30d15-b696-4358-aaea-1cc966b800af
-- title:
--   P2 M Ground Theory Heights  Heights is Weighted Homogeneous in Group of dvd 78c37585d297: P2 M Ground Theory Heights  Heights is Weighted Homogeneous in Group of dvd 78c37585d297
-- statement:
--   The P2 M Ground Theory Heights  Heights is Weighted Homogeneous in Group of dvd 78c37585d297 construction uses the P2 M Ground Theory Heights  Heights is Weighted Homogeneous in Group of dvd 78c37585d297 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L217-L222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
open MvPolynomial
noncomputable section
variable {k n : ℕ} {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297 {f g : MvPolynomial (Fin k × Fin n) F} {δ : ℕ}
    (hf : IsMultiHomog δ f) (hf0 : f ≠ 0) (hgf : g ∣ f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup i) g a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isWeightedHomogeneous_inGroup_of_dvd» := P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_inGroup_of_dvd_78c37585d297
