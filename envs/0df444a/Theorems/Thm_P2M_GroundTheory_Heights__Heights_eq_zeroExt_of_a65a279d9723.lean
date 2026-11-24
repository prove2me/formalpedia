-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723
-- name    : P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:38.280171+00:00
-- url     : https://prove2.me/theorems/374c7945-ac61-4ab4-bfc9-d6dacbb141a0
-- title:
--   P2 M Ground Theory Heights  Heights eq zero Ext of a65a279d9723: P2 M Ground Theory Heights  Heights eq zero Ext of a65a279d9723
-- statement:
--   The P2 M Ground Theory Heights  Heights eq zero Ext of a65a279d9723 construction uses the P2 M Ground Theory Heights  Heights eq zero Ext of a65a279d9723 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L87-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723 {m k : ℕ} {y : EuclideanSpace ℂ (Fin (m + k))}
    (hy : ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0) :
    y = zeroExt m k (WithLp.toLp 2 fun i => y (Fin.castAdd k i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eq_zeroExt_of» := P2M_GroundTheory_Heights__Heights_eq_zeroExt_of_a65a279d9723
