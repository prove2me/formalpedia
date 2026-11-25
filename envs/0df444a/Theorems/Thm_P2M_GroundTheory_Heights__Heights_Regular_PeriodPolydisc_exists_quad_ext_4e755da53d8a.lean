-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:53.309796+00:00
-- url     : https://prove2.me/theorems/2f7b7026-3f89-4810-a9b3-5042ffd811bb
-- title:
--   P2 M Ground Theory Heights  Heights Regular Period Polydisc exists quad ext 4e755da53d8a: P2 M Ground Theory Heights  Heights Regular Period Polydisc exists quad ext 4e755da53d8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Period Polydisc exists quad ext 4e755da53d8a construction uses the P2 M Ground Theory Heights  Heights Regular Period Polydisc exists quad ext 4e755da53d8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L227-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L227-L266

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

theorem P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a (h0 : ExpQuadMonomial.Statement) (v : Fin g → ℤ) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ ∀ w ∈ logCover P.a_le,
      Q (expCover a w) = (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PeriodPolydisc».«exists_quad_ext» := P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a
