-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac
-- name    : P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:16.735355+00:00
-- url     : https://prove2.me/theorems/91161037-1a25-4b2b-8996-b664f869d950
-- title:
--   P2 M Ground Theory Heights  Heights chow Ht pow 660460443bac: P2 M Ground Theory Heights  Heights chow Ht pow 660460443bac
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Ht pow 660460443bac construction uses the P2 M Ground Theory Heights  Heights chow Ht pow 660460443bac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L149-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L149-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} (d : ℕ)
    {g : MvPolynomial (Fin k × Fin n) K} (hg : g ≠ 0) (m : ℕ) :
    chowHt H k (m * d) (g ^ m) = m * chowHt H k d g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowHt_pow» := P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac
