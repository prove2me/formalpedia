-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_derOp_hasDeriv
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.derOp_hasDeriv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:47.084593+00:00
-- url     : https://prove2.me/theorems/fd3228eb-13d9-4310-83cd-c6931267b960
-- title:
--   HW: der Op has Deriv
-- statement:
--   The HW construction uses the der Op has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelDer.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelDer.lean#L105-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem ReciprocityTheory.ChartRestriction.DS.HW.derOp_hasDeriv [FiniteDimensional ℂ V] (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V))
    (hcont : Continuous τ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (derOp ε τ X) 0 := by sorry
