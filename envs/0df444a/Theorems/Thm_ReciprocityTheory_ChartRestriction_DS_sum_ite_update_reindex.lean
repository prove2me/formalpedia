-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_ite_update_reindex
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_ite_update_reindex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:20.988906+00:00
-- url     : https://prove2.me/theorems/3edc9bab-69e7-51ac-803c-4e678fa45b32
-- title:
--   DS: sum ite update reindex
-- statement:
--   The DS construction uses the sum ite update reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L81-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.sum_ite_update_reindex {k : ℕ} (i : Fin k) (P Q : Fin n × Fin n → Prop) [DecidablePred P]
    [DecidablePred Q] (f g : Fin n × Fin n → Fin n × Fin n) (hf : ∀ p, P p → Q (f p))
    (hg : ∀ p, Q p → P (g p)) (hgf : ∀ p, P p → g (f p) = p) (hfg : ∀ p, Q p → f (g p) = p)
    (W : (Fin k → Fin n × Fin n) → Module.End ℂ M) (F : Big n k M) :
    ∑ κ, (if P (κ i) then W κ (F (Function.update κ i (f (κ i)))) else 0) =
      ∑ κ, (if Q (κ i) then W (Function.update κ i (g (κ i))) (F κ) else 0) := by sorry
