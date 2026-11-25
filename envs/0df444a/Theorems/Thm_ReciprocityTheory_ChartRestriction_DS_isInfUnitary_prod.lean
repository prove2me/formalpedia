-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isInfUnitary_prod
-- name    : ReciprocityTheory.ChartRestriction.DS.isInfUnitary_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:55.591163+00:00
-- url     : https://prove2.me/theorems/098f7d30-99ec-5a4a-bb38-94c34d4aea6e
-- title:
--   DS: is Inf Unitary prod
-- statement:
--   The DS construction uses the is Inf Unitary prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreB.lean#L92-L101

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
variable {M₁ M₂ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] [NormedAddCommGroup M₂]
  [InnerProductSpace ℂ M₂] {ε : Fin n → Bool}
  {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem ReciprocityTheory.ChartRestriction.DS.isInfUnitary_prod (hU₁ : IsInfUnitary ε E₁) (hU₂ : IsInfUnitary ε E₂) :
    IsInfUnitary ε (prodE E₁ E₂) := by sorry
