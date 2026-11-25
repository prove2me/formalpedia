-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:44.627797+00:00
-- url     : https://prove2.me/theorems/266133cc-6b7e-468d-a4ac-8d4bce90473a
-- title:
--   P2 M Ground Theory Heights  Heights Log Int log Norm T insert of homog 2a3a2a583f23: P2 M Ground Theory Heights  Heights Log Int log Norm T insert of homog 2a3a2a583f23
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int log Norm T insert of homog 2a3a2a583f23 construction uses the P2 M Ground Theory Heights  Heights Log Int log Norm T insert of homog 2a3a2a583f23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L218-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L218-L269

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23 (h : HermNorm n) (r : ℝ) (T : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ T) (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) (d : ℕ)
    (hd : IsWeightedHomogeneous (indW (inGroup i)) g d)
    (ih1 : IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ r))
    (ih2 : ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h T u) g ≠ 0) :
    IntegrableOn (fun u => Real.log ‖eval (normT h (insert i T) u) g‖) (polydisc _ r) ∧
      ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) r)), eval (normT h (insert i T) u) g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«logNormT_insert_of_homog» := P2M_GroundTheory_Heights__Heights_LogInt_logNormT_insert_of_homog_2a3a2a583f23
