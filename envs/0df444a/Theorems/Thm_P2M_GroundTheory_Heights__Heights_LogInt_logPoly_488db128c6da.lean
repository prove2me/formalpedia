-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:24.843717+00:00
-- url     : https://prove2.me/theorems/8d32d776-89fb-4e82-a7d4-40c56495e1ba
-- title:
--   P2 M Ground Theory Heights  Heights Log Int log Poly 488db128c6da: P2 M Ground Theory Heights  Heights Log Int log Poly 488db128c6da
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int log Poly 488db128c6da construction uses the P2 M Ground Theory Heights  Heights Log Int log Poly 488db128c6da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L205-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L205-L275

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da [Fintype ι] [DecidableEq ι] (r : ℝ) :
    ∀ (N : ℕ) (g : MvPolynomial ι ℂ), (nonHomog g).card = N → g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval u g‖) (polydisc ι r) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc ι r)), eval u g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«logPoly» := P2M_GroundTheory_Heights__Heights_LogInt_logPoly_488db128c6da
