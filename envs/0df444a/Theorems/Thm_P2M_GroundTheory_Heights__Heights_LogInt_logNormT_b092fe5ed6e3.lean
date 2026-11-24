-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:40.22007+00:00
-- url     : https://prove2.me/theorems/5d2e4923-49a1-4bcf-9eea-401f70600f16
-- title:
--   P2 M Ground Theory Heights  Heights Log Int log Norm T b092fe5ed6e3: P2 M Ground Theory Heights  Heights Log Int log Norm T b092fe5ed6e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int log Norm T b092fe5ed6e3 construction uses the P2 M Ground Theory Heights  Heights Log Int log Norm T b092fe5ed6e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L271-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L271-L313

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3 (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k)) :
    ∀ g : MvPolynomial (Fin k × Fin n) ℂ, g ≠ 0 →
      IntegrableOn (fun u => Real.log ‖eval (normT h T u) g‖) (polydisc _ C) ∧
        ∀ᵐ u ∂(volume.restrict (polydisc (Fin k × Fin n) C)), eval (normT h T u) g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«logNormT» := P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3
