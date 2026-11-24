-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33
-- name    : P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:08.512908+00:00
-- url     : https://prove2.me/theorems/c6b711fc-560f-4f64-9a69-9cb5571f7f6a
-- title:
--   P2 M Ground Theory Heights  Heights MCSchur herm Value eq qf 16537984ce33: P2 M Ground Theory Heights  Heights MCSchur herm Value eq qf 16537984ce33
-- statement:
--   The P2 M Ground Theory Heights  Heights MCSchur herm Value eq qf 16537984ce33 construction uses the P2 M Ground Theory Heights  Heights MCSchur herm Value eq qf 16537984ce33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    hermValue A w = qf A (fun k => (w k).re) + qf A (fun k => (w k).im) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCSchur».«hermValue_eq_qf» := P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33
