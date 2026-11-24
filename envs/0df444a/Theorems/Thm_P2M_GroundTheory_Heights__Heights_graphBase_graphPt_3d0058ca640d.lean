-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d
-- name    : P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:15.844796+00:00
-- url     : https://prove2.me/theorems/78438c64-ad46-4eb1-aa64-fd2f85863958
-- title:
--   P2 M Ground Theory Heights  Heights graph Base graph Pt 3d0058ca640d: P2 M Ground Theory Heights  Heights graph Base graph Pt 3d0058ca640d
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Base graph Pt 3d0058ca640d construction uses the P2 M Ground Theory Heights  Heights graph Base graph Pt 3d0058ca640d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) (x : EuclideanSpace ℂ (Fin d)) :
    graphBase e (graphPt e F x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphBase_graphPt» := P2M_GroundTheory_Heights__Heights_graphBase_graphPt_3d0058ca640d
