-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4
-- name    : P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:11.301691+00:00
-- url     : https://prove2.me/theorems/4e25247c-4322-5112-8978-cfcc31888f61
-- title:
--   P2 M Ground Theory Heights  Heights Period Herm Value im eq c5f7a90330b4: P2 M Ground Theory Heights  Heights Period Herm Value im eq c5f7a90330b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Herm Value im eq c5f7a90330b4 construction uses the P2 M Ground Theory Heights  Heights Period Herm Value im eq c5f7a90330b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodHermValue.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodHermValue.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodHermValue
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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PeriodHermValue

theorem P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4 {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).im) =
      τ.map Complex.im *ᵥ β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodHermValue».«im_eq» := P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4
