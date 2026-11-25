-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:31.305398+00:00
-- url     : https://prove2.me/theorems/4668a0f2-89b3-49a1-9ed4-2ec2a2fe55a2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Period Polydisc exp quadratic tau shifted d0d1d6cc101f: P2 M Ground Theory Heights  Heights Regular Period Polydisc exp quadratic tau shifted d0d1d6cc101f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Period Polydisc exp quadratic tau shifted d0d1d6cc101f construction uses the P2 M Ground Theory Heights  Heights Regular Period Polydisc exp quadratic tau shifted d0d1d6cc101f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L198-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L198-L221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)

theorem P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f (v : Fin g → ℤ) (hnn : ∀ i, 0 ≤ intQuad (P.B i) v) (h : (Fin n → ℂ) → ℂ)
    (w : Fin n → ℂ)
    (hw : Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ fun k => (v k : ℂ))) =
      (∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat) *
        h (expCover a w)) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ))) = h (expCover a w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PeriodPolydisc».«exp_quadratic_tau_shifted» := P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f
