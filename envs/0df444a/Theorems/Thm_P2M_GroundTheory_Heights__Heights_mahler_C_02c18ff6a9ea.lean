-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
-- name    : P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:15.887465+00:00
-- url     : https://prove2.me/theorems/d608618a-7101-40b9-9b37-358941f9ba56
-- title:
--   P2 M Ground Theory Heights  Heights mahler C 02c18ff6a9ea: P2 M Ground Theory Heights  Heights mahler C 02c18ff6a9ea
-- statement:
--   The P2 M Ground Theory Heights  Heights mahler C 02c18ff6a9ea construction uses the P2 M Ground Theory Heights  Heights mahler C 02c18ff6a9ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L85-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea (h : HermNorm n) (k : ℕ) (z : ℂ) :
    mahler h k (C z : MvPolynomial (Fin k × Fin n) ℂ) = Real.log ‖z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mahler_C» := P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
