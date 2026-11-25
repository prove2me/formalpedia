-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:13.583371+00:00
-- url     : https://prove2.me/theorems/577b4a69-b4b0-4f9c-8ba8-0a9498a1f202
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map row Form 244e4b4b8f4b: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map row Form 244e4b4b8f4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map row Form 244e4b4b8f4b construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map row Form 244e4b4b8f4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L75-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
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
open GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b (i : Fin d) : backMap J d q k (rowForm J d q k i) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«backMap_rowForm» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_rowForm_244e4b4b8f4b
