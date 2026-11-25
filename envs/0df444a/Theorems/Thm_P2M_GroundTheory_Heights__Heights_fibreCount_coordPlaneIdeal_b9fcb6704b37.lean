-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
-- name    : P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:28.604529+00:00
-- url     : https://prove2.me/theorems/d5113a4c-beb4-4822-9ab8-f548b29348db
-- title:
--   P2 M Ground Theory Heights  Heights fibre Count coord Plane Ideal b9fcb6704b37: P2 M Ground Theory Heights  Heights fibre Count coord Plane Ideal b9fcb6704b37
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Count coord Plane Ideal b9fcb6704b37 construction uses the P2 M Ground Theory Heights  Heights fibre Count coord Plane Ideal b9fcb6704b37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L113-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L113-L137

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

theorem P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37 {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ)
    (hπ : (coordPlaneBlock π).det ≠ 0) (w : EuclideanSpace ℂ (Fin m)) :
    fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreCount_coordPlaneIdeal» := P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
