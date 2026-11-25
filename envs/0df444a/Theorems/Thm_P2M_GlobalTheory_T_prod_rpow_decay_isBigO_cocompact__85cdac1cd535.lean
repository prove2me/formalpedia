-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_prod_rpow_decay_isBigO_cocompact__85cdac1cd535
-- name    : P2M_GlobalTheory_T_prod_rpow_decay_isBigO_cocompact__85cdac1cd535
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:09.546024+00:00
-- url     : https://prove2.me/theorems/b4c4c11b-f1b2-481f-ab45-1b7c114cd5e0
-- title:
--   P2 M Global Theory T prod rpow decay is Big O cocompact  85cdac1cd535: P2 M Global Theory T prod rpow decay is Big O cocompact  85cdac1cd535
-- statement:
--   The P2 M Global Theory T prod rpow decay is Big O cocompact  85cdac1cd535 construction uses the P2 M Global Theory T prod rpow decay is Big O cocompact  85cdac1cd535 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdRpowDecayIsBigOCocompactStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdRpowDecayIsBigOCocompactStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_prod_rpow_decay_isBigO_cocompact__85cdac1cd535 : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by sorry

alias «GlobalTheory».«T».«prod_rpow_decay_isBigO_cocompact'» := P2M_GlobalTheory_T_prod_rpow_decay_isBigO_cocompact__85cdac1cd535
