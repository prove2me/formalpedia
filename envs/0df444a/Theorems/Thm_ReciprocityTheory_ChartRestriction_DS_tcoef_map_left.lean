-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_map_left
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_map_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:34.494605+00:00
-- url     : https://prove2.me/theorems/cb4ffe59-f596-47fa-82b4-ac61f8c569c2
-- title:
--   DS: tcoef map left
-- statement:
--   The DS construction uses the tcoef map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L18-L24

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

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_map_left {M' : Type*} [AddCommGroup M'] [Module ℂ M'] (φ : Module.Dual ℂ (Fock n))
    (T : M' →ₗ[ℂ] M) (y : TensorProduct ℂ M' (Fock n)) :
    tcoef φ (TensorProduct.map T LinearMap.id y) = T (tcoef φ y) := by sorry
