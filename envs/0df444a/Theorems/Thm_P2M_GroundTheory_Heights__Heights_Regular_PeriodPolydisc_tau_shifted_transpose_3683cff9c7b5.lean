-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:40.607928+00:00
-- url     : https://prove2.me/theorems/dbae05e1-c280-59b7-aabe-3f6dabe0faa2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Period Polydisc tau shifted transpose 3683cff9c7b5: P2 M Ground Theory Heights  Heights Regular Period Polydisc tau shifted transpose 3683cff9c7b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Period Polydisc tau shifted transpose 3683cff9c7b5 construction uses the P2 M Ground Theory Heights  Heights Regular Period Polydisc tau shifted transpose 3683cff9c7b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L223-L225

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

theorem P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5 {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) : (P.tau0 w)ᵀ = P.tau0 w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PeriodPolydisc».«tau_shifted_transpose» := P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5
