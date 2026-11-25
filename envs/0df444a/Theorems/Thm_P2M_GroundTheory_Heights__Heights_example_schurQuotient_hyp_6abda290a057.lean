-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_example_schurQuotient_hyp_6abda290a057
-- name    : P2M_GroundTheory_Heights__Heights_example_schurQuotient_hyp_6abda290a057
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:27.161605+00:00
-- url     : https://prove2.me/theorems/30ed4142-2a49-540c-a27a-6ee08cbb6155
-- title:
--   P2 M Ground Theory Heights  Heights example schur Quotient hyp 6abda290a057: P2 M Ground Theory Heights  Heights example schur Quotient hyp 6abda290a057
-- statement:
--   The P2 M Ground Theory Heights  Heights example schur Quotient hyp 6abda290a057 construction uses the P2 M Ground Theory Heights  Heights example schur Quotient hyp 6abda290a057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Statements.lean#L280-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Statements.lean#L280-L282

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
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

theorem P2M_GroundTheory_Heights__Heights_example_schurQuotient_hyp_6abda290a057 :
    (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 2))).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«example_schurQuotient_hyp» := P2M_GroundTheory_Heights__Heights_example_schurQuotient_hyp_6abda290a057
