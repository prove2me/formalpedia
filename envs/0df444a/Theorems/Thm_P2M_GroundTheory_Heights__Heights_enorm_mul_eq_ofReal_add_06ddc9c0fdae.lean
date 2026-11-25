-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae
-- name    : P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:28.467592+00:00
-- url     : https://prove2.me/theorems/b44f1dad-d762-44f8-8526-e1ea6a69d687
-- title:
--   P2 M Ground Theory Heights  Heights enorm mul eq of Real add 06ddc9c0fdae: P2 M Ground Theory Heights  Heights enorm mul eq of Real add 06ddc9c0fdae
-- statement:
--   The P2 M Ground Theory Heights  Heights enorm mul eq of Real add 06ddc9c0fdae construction uses the P2 M Ground Theory Heights  Heights enorm mul eq of Real add 06ddc9c0fdae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
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
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae {a r : ℝ} (hr : 0 ≤ r) :
    ‖a * r‖ₑ = ENNReal.ofReal a * ENNReal.ofReal r + ENNReal.ofReal (-a) * ENNReal.ofReal r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«enorm_mul_eq_ofReal_add» := P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae
