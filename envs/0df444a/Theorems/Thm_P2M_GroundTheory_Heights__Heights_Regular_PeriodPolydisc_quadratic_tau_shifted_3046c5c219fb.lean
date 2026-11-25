-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:27.6556+00:00
-- url     : https://prove2.me/theorems/71577b9e-8533-440b-b430-10953a9c27fc
-- title:
--   P2 M Ground Theory Heights  Heights Regular Period Polydisc quadratic tau shifted 3046c5c219fb: P2 M Ground Theory Heights  Heights Regular Period Polydisc quadratic tau shifted 3046c5c219fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Period Polydisc quadratic tau shifted 3046c5c219fb construction uses the P2 M Ground Theory Heights  Heights Regular Period Polydisc quadratic tau shifted 3046c5c219fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L190-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L190-L196

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

theorem P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb (v : Fin g → ℤ) (w : Fin n → ℂ) :
    (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ (fun k => (v k : ℂ)) =
      (fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ (fun k => (v k : ℂ)) -
        ∑ i : Fin a, w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) *
          ((intQuad (P.B i) v : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PeriodPolydisc».«quadratic_tau_shifted» := P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb
