-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:02.986183+00:00
-- url     : https://prove2.me/theorems/77e46a5a-80b5-5fc1-a6d2-2b57e7dd0599
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Num Poly LT sum 9991b4d10672: P2 M Ground Theory Heights  Heights Kleiman is Num Poly LT sum 9991b4d10672
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Num Poly LT sum 9991b4d10672 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Num Poly LT sum 9991b4d10672 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L123-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672 {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isNumPolyLT_sum» := P2M_GroundTheory_Heights__Heights_Kleiman_isNumPolyLT_sum_9991b4d10672
