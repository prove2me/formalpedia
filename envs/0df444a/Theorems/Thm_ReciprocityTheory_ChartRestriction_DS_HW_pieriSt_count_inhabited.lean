-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_count_inhabited
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_count_inhabited
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:04:53.080929+00:00
-- url     : https://prove2.me/theorems/5e762979-76ee-47c5-829c-8fc70b656ece
-- title:
--   HW: pieri St count inhabited
-- statement:
--   The HW construction uses the pieri St count inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L71-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L71-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest
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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_count_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : KG ε =>
      (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) k : unitary (Matrix Unit Unit ℂ)) : Matrix Unit Unit ℂ)) ∧
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ =>
        (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) (γ t) : unitary (Matrix Unit Unit ℂ)) :
          Matrix Unit Unit ℂ) i j)
        ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) X i j) 0) ∧
    Formalism.REAL.KRel ε (fun a b => (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) ∧
    (∀ a, (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1) =
      Matrix.diagonal fun i => (((fun _ : Unit => (0 : Fin n → ℝ)) i a : ℝ) : ℂ)) ∧
    Function.Injective (fun _ : Unit => (0 : Fin n → ℝ)) ∧
    (∑ i : Unit, weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) =
      (Fintype.card Unit : ℝ) * weylK ε 0) ∧
    (∀ i : Unit, ¬ KDom ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) →
      weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) = 0) ∧
    Nonempty (KType ε 0) := by sorry
