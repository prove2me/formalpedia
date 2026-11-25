-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:39.040772+00:00
-- url     : https://prove2.me/theorems/1ddcbdb0-4860-4c51-a1d2-5c1c372c2d11
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt det one add eq sum 64ef61237c7b: P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt det one add eq sum 64ef61237c7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt det one add eq sum 64ef61237c7b construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt det one add eq sum 64ef61237c7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) :
    (1 + X).det = ∑ s : Finset n, (X.submatrix ((↑) : s → n) ((↑) : s → n)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetMinorsAlt».«det_one_add_eq_sum» := P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b
