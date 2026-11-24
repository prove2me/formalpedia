-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:51.191601+00:00
-- url     : https://prove2.me/theorems/a9a04ba5-90a3-4ef0-9326-16f70c65960f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms choose two add d3d2161255a9: P2 M Ground Theory Heights  Heights Rest Terms choose two add d3d2161255a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms choose two add d3d2161255a9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms choose two add d3d2161255a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PRestPolynomialHomogeneous.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PRestPolynomialHomogeneous.lean#L9-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9 (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«choose_two_add» := P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9
