-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaFibre_differentiableAt_graphPt_4ee4476b47eb
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaFibre_differentiableAt_graphPt_4ee4476b47eb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:34.084302+00:00
-- url     : https://prove2.me/theorems/5887536a-849e-4449-9a41-e755740b0830
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Fibre differentiable At graph Pt 4ee4476b47eb: P2 M Ground Theory Heights  Heights Graph Area Fibre differentiable At graph Pt 4ee4476b47eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Fibre differentiable At graph Pt 4ee4476b47eb construction uses the P2 M Ground Theory Heights  Heights Graph Area Fibre differentiable At graph Pt 4ee4476b47eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaFibre.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaFibre.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGraphAreaFibre
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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_GraphAreaFibre_differentiableAt_graphPt_4ee4476b47eb {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hΦ : DifferentiableAt ℂ Φ x) : DifferentiableAt ℂ (graphPt e Φ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaFibre».«differentiableAt_graphPt» := P2M_GroundTheory_Heights__Heights_GraphAreaFibre_differentiableAt_graphPt_4ee4476b47eb
