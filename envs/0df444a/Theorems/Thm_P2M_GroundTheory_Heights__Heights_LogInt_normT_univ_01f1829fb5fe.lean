-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:39.791894+00:00
-- url     : https://prove2.me/theorems/2c67ca54-de61-49e6-9455-487b9eda84d1
-- title:
--   P2 M Ground Theory Heights  Heights Log Int norm T univ 01f1829fb5fe: P2 M Ground Theory Heights  Heights Log Int norm T univ 01f1829fb5fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int norm T univ 01f1829fb5fe construction uses the P2 M Ground Theory Heights  Heights Log Int norm T univ 01f1829fb5fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«normT_univ» := P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe
