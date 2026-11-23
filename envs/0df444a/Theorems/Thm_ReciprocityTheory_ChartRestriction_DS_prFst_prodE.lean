-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_prodE
-- name    : ReciprocityTheory.ChartRestriction.DS.prFst_prodE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:55.756742+00:00
-- url     : https://prove2.me/theorems/3ec4db09-eba7-46ad-87c8-919e1a2cf598
-- title:
--   DS: pr Fst prod E
-- statement:
--   The DS construction uses the pr Fst prod E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L65-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
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
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem ReciprocityTheory.ChartRestriction.DS.prFst_prodE (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prFst (prodE E₁ E₂ a b x) = E₁ a b (prFst x) := by sorry
