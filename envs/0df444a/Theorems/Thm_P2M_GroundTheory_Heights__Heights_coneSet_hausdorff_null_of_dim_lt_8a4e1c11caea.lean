-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea
-- name    : P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:31.745093+00:00
-- url     : https://prove2.me/theorems/92384d65-064e-5d08-b256-ba8b563fadd2
-- title:
--   P2 M Ground Theory Heights  Heights cone Set hausdorff null of dim lt 8a4e1c11caea: P2 M Ground Theory Heights  Heights cone Set hausdorff null of dim lt 8a4e1c11caea
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Set hausdorff null of dim lt 8a4e1c11caea construction uses the P2 M Ground Theory Heights  Heights cone Set hausdorff null of dim lt 8a4e1c11caea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeGraphCover.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeGraphCover.lean#L17-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeGraphCover
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneSet_hausdorff_null_of_dim_lt» := P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea
