-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_extract
-- name    : ReciprocityTheory.ChartRestriction.DS.khw_extract
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:06.480502+00:00
-- url     : https://prove2.me/theorems/ed7bdbc9-fba8-40dd-b90e-f2dcbe171c80
-- title:
--   DS: khw extract
-- statement:
--   The DS construction uses the khw extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L113-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L113-L172

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

theorem ReciprocityTheory.ChartRestriction.DS.khw_extract (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {y : TensorProduct ℂ M (Fock n)}
    (hy : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) μ y) (hy0 : y ≠ 0) :
    ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0 ∧
      IsKHWVec ε E (μ - fockWt ε s) (tcoef ((fockBasis n).coord s) y) := by sorry
