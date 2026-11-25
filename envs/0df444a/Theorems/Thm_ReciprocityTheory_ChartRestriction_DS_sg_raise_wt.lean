-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_raise_wt
-- name    : ReciprocityTheory.ChartRestriction.DS.sg_raise_wt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:44.739221+00:00
-- url     : https://prove2.me/theorems/e8bdbdce-df41-4f8a-ba4e-450e24ce9b30
-- title:
--   DS: sg raise wt
-- statement:
--   The DS construction uses the sg raise wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L86-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L86-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.sg_raise_wt (ε : Fin n → Bool) {a b : Fin n} (hab : a ≠ b) (hε : ε a = ε b) {ν : Fin n → ℝ}
    {f : Fock n} (hf : ∀ c, sgE ε cpFock cmFock c c f = ((ν c : ℝ) : ℂ) • f) (c : Fin n) :
    sgE ε cpFock cmFock c c (sgE ε cpFock cmFock a b f) =
      (((ν + root a b) c : ℝ) : ℂ) • sgE ε cpFock cmFock a b f := by sorry
