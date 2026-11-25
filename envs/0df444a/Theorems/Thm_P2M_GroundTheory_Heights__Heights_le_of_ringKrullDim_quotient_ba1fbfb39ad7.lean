-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_of_ringKrullDim_quotient_ba1fbfb39ad7
-- name    : P2M_GroundTheory_Heights__Heights_le_of_ringKrullDim_quotient_ba1fbfb39ad7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:19.71329+00:00
-- url     : https://prove2.me/theorems/eb8e484a-895b-4505-9789-56f561c44b27
-- title:
--   P2 M Ground Theory Heights  Heights le of ring Krull Dim quotient ba1fbfb39ad7: P2 M Ground Theory Heights  Heights le of ring Krull Dim quotient ba1fbfb39ad7
-- statement:
--   The P2 M Ground Theory Heights  Heights le of ring Krull Dim quotient ba1fbfb39ad7 construction uses the P2 M Ground Theory Heights  Heights le of ring Krull Dim quotient ba1fbfb39ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
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
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_le_of_ringKrullDim_quotient_ba1fbfb39ad7 {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_of_ringKrullDim_quotient» := P2M_GroundTheory_Heights__Heights_le_of_ringKrullDim_quotient_ba1fbfb39ad7
