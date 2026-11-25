-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tens_khw_vanish
-- name    : ReciprocityTheory.ChartRestriction.DS.tens_khw_vanish
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:26.813536+00:00
-- url     : https://prove2.me/theorems/6861e27a-8553-5f88-aef8-9e6f657fa41f
-- title:
--   DS: tens khw vanish
-- statement:
--   The DS construction uses the tens khw vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L252-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L252-L307

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.tens_khw_vanish {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0)
    {t : ℂ} (ht : t ≠ ∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map (layer ε E V 1 ⊓ LinearMap.ker (zPlus ε E - t • 1)).subtype
      (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (hK : IsKHWVec ε (fun a b => (TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))))
      (lam - rhoC ε + rhoHol ε) y) : y = 0 := by sorry
