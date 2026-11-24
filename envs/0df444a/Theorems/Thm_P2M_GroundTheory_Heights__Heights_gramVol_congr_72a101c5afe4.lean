-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4
-- name    : P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:08.497612+00:00
-- url     : https://prove2.me/theorems/0ba99a8e-7427-4ab6-b33f-722a0f94ffc8
-- title:
--   P2 M Ground Theory Heights  Heights gram Vol congr 72a101c5afe4: P2 M Ground Theory Heights  Heights gram Vol congr 72a101c5afe4
-- statement:
--   The P2 M Ground Theory Heights  Heights gram Vol congr 72a101c5afe4 construction uses the P2 M Ground Theory Heights  Heights gram Vol congr 72a101c5afe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetAreaLintegral.lean#L16-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal

theorem P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4 {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gramVol_congr» := P2M_GroundTheory_Heights__Heights_gramVol_congr_72a101c5afe4
