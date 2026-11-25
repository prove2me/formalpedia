-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensKRep_units
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.tensKRep_units
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:33.707942+00:00
-- url     : https://prove2.me/theorems/8e1602f3-c71b-50f2-a852-87b2e8048f79
-- title:
--   HW: tens KRep units
-- statement:
--   The HW construction uses the tens KRep units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepB.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepB.lean#L103-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.HW.tensKRep_units (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) :
    (tensKRep T ρ dρ hc hd).units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) := by sorry
