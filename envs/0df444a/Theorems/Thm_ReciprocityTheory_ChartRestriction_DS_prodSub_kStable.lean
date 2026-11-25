-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prodSub_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.prodSub_kStable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:39.532832+00:00
-- url     : https://prove2.me/theorems/d72eb6b4-5a23-473b-ab06-00a11554e725
-- title:
--   DS: prod Sub k Stable
-- statement:
--   The DS construction uses the prod Sub k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCore.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCore.lean#L43-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
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

theorem ReciprocityTheory.ChartRestriction.DS.prodSub_kStable {ε : Fin n → Bool} {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    {E₂ : Fin n → Fin n → Module.End ℂ M₂} {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂}
    (h₁ : IsKStableSub ε E₁ V₁) (h₂ : IsKStableSub ε E₂ V₂) :
    IsKStableSub ε (prodE E₁ E₂) (prodSub V₁ V₂) := by sorry
