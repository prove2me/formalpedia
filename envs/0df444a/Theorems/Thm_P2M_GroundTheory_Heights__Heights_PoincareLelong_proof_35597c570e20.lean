-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PoincareLelong_proof_35597c570e20
-- name    : P2M_GroundTheory_Heights__Heights_PoincareLelong_proof_35597c570e20
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:34:03.324782+00:00
-- url     : https://prove2.me/theorems/b9687360-8128-4ee5-9741-dc62e572af7c
-- title:
--   P2 M Ground Theory Heights  Heights Poincare Lelong proof 35597c570e20: P2 M Ground Theory Heights  Heights Poincare Lelong proof 35597c570e20
-- statement:
--   The P2 M Ground Theory Heights  Heights Poincare Lelong proof 35597c570e20 construction uses the P2 M Ground Theory Heights  Heights Poincare Lelong proof 35597c570e20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPoincareLelong.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPoincareLelong.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPoincareLelong
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_PoincareLelong_proof_35597c570e20 (hStokes : StokesOnVariety.Statement)
    (hReg : LelongRegularise.Statement) (hLim : LelongLimit.Statement) :
    PoincareLelong.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PoincareLelong».«proof» := P2M_GroundTheory_Heights__Heights_PoincareLelong_proof_35597c570e20
