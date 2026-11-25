-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902
-- name    : P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:46.277748+00:00
-- url     : https://prove2.me/theorems/46ed7084-5bcd-40bf-8860-06ac1778cd65
-- title:
--   P2 M Ground Theory Heights  Heights MCSchur qf is Least 1f825f941902: P2 M Ground Theory Heights  Heights MCSchur qf is Least 1f825f941902
-- statement:
--   The P2 M Ground Theory Heights  Heights MCSchur qf is Least 1f825f941902 construction uses the P2 M Ground Theory Heights  Heights MCSchur qf is Least 1f825f941902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L43-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L43-L74

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
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902 (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (c : n → ℝ) :
    IsLeast (Set.range fun a : m → ℝ => qf Y⁻¹ (Sum.elim a c)) (qf (Y.toBlocks₂₂)⁻¹ c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCSchur».«qf_isLeast» := P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902
