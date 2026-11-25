-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9
-- name    : P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:55.920525+00:00
-- url     : https://prove2.me/theorems/9d34b55a-2ccc-427e-9a1f-0163d27e83a5
-- title:
--   P2 M Reciprocity Theory An Form A Psh Inh ii sup  a1047692b6a9: P2 M Reciprocity Theory An Form A Psh Inh ii sup  a1047692b6a9
-- statement:
--   The P2 M Reciprocity Theory An Form A Psh Inh ii sup  a1047692b6a9 construction uses the P2 M Reciprocity Theory An Form A Psh Inh ii sup  a1047692b6a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L189-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L189-L200

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section

theorem P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9 {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ j, IntervalIntegrable (f j) volume a b) :
    IntervalIntegrable (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ))
      volume a b := by sorry

alias «ReciprocityTheory».«AnForm».«A».«PshInh».«ii_sup'» := P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9
