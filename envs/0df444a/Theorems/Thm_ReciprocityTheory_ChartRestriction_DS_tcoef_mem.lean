-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:15.061414+00:00
-- url     : https://prove2.me/theorems/c7d46e1c-2ab7-4cd5-94d2-39ace2d1b920
-- title:
--   DS: tcoef mem
-- statement:
--   The DS construction uses the tcoef mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L51-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_mem {L : Submodule ℂ M} {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (φ : Module.Dual ℂ (Fock n)) : tcoef φ y ∈ L := by sorry
