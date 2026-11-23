-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_cp_cm_basis
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_cp_cm_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:40.474409+00:00
-- url     : https://prove2.me/theorems/2e65a128-d1b6-4a39-905a-233c9eee7e51
-- title:
--   DS: lf cp cm basis
-- statement:
--   The DS construction uses the lf cp cm basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L76-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
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

theorem ReciprocityTheory.ChartRestriction.DS.lf_cp_cm_basis {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) ∧
      cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) = σ • fockBasis n S := by sorry
