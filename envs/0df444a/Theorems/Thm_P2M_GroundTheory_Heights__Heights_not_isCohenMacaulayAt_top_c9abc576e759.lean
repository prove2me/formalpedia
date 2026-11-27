-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_isCohenMacaulayAt_top_c9abc576e759
-- name    : P2M_GroundTheory_Heights__Heights_not_isCohenMacaulayAt_top_c9abc576e759
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:23.316565+00:00
-- url     : https://prove2.me/theorems/ab623335-87ee-5a0b-84c6-3537adda15aa
-- title:
--   P2 M Ground Theory Heights  Heights not is Cohen Macaulay At top c9abc576e759: P2 M Ground Theory Heights  Heights not is Cohen Macaulay At top c9abc576e759
-- statement:
--   The P2 M Ground Theory Heights  Heights not is Cohen Macaulay At top c9abc576e759 construction uses the P2 M Ground Theory Heights  Heights not is Cohen Macaulay At top c9abc576e759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTransverseObjects.lean#L40-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_not_isCohenMacaulayAt_top_c9abc576e759 (q : Fin n → ℂ) :
    ¬ IsCohenMacaulayAt (⊤ : Ideal (MvPolynomial (Fin n) ℂ)) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_isCohenMacaulayAt_top» := P2M_GroundTheory_Heights__Heights_not_isCohenMacaulayAt_top_c9abc576e759
