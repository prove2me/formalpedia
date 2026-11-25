-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_iteratedFDeriv_iteratedFDeriv__4a3cde79c1c2
-- name    : P2M_GlobalTheory_T_norm_iteratedFDeriv_iteratedFDeriv__4a3cde79c1c2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:14.8995+00:00
-- url     : https://prove2.me/theorems/7c205eaa-ab90-4978-aee4-2a46fac794fd
-- title:
--   P2 M Global Theory T norm iterated FDeriv iterated FDeriv  4a3cde79c1c2: P2 M Global Theory T norm iterated FDeriv iterated FDeriv  4a3cde79c1c2
-- statement:
--   The P2 M Global Theory T norm iterated FDeriv iterated FDeriv  4a3cde79c1c2 construction uses the P2 M Global Theory T norm iterated FDeriv iterated FDeriv  4a3cde79c1c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivIteratedFDerivStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivIteratedFDerivStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDerivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_iteratedFDeriv_iteratedFDeriv__4a3cde79c1c2 : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by sorry

alias «GlobalTheory».«T».«norm_iteratedFDeriv_iteratedFDeriv'» := P2M_GlobalTheory_T_norm_iteratedFDeriv_iteratedFDeriv__4a3cde79c1c2
