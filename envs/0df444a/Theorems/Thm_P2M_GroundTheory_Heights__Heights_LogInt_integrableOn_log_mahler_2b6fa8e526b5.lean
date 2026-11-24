-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:45.760254+00:00
-- url     : https://prove2.me/theorems/5d5d7669-21cd-4812-ae70-7df6acf58a74
-- title:
--   P2 M Ground Theory Heights  Heights Log Int integrable On log mahler 2b6fa8e526b5: P2 M Ground Theory Heights  Heights Log Int integrable On log mahler 2b6fa8e526b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int integrable On log mahler 2b6fa8e526b5 construction uses the P2 M Ground Theory Heights  Heights Log Int integrable On log mahler 2b6fa8e526b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L38-L48

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5 (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«integrableOn_log_mahler» := P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5
