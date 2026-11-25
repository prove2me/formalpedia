-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286
-- name    : P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:37.686804+00:00
-- url     : https://prove2.me/theorems/03367762-2048-41e0-ade0-ba6d8f9223e1
-- title:
--   P2 M Ground Theory Heights  Heights MCSchur herm Value is Least 2b30b119e286: P2 M Ground Theory Heights  Heights MCSchur herm Value is Least 2b30b119e286
-- statement:
--   The P2 M Ground Theory Heights  Heights MCSchur herm Value is Least 2b30b119e286 construction uses the P2 M Ground Theory Heights  Heights MCSchur herm Value is Least 2b30b119e286 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L76-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/HermValueIsLeast.lean#L76-L96

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

theorem P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286 (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (v : n → ℂ) :
    IsLeast (Set.range fun x : m → ℂ => hermValue Y⁻¹ (Sum.elim x v))
      (hermValue (Y.toBlocks₂₂)⁻¹ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCSchur».«hermValue_isLeast» := P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286
