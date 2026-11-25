-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pieriSt_cartan_inhabited
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_cartan_inhabited
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:40.035667+00:00
-- url     : https://prove2.me/theorems/75334d90-3924-5fb4-a7fe-034625ac152d
-- title:
--   HW: pieri St cartan inhabited
-- statement:
--   The HW construction uses the pieri St cartan inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/StTest.lean#L99-L109

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_cartan_inhabited {n : ℕ} (ε : Fin n → Bool) :
    (∀ a : Fin n, ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1)) *ᵥ
      (fun _ : Unit => (1 : ℂ)) = (((0 : Fin n → ℝ) a : ℝ) : ℂ) • (fun _ : Unit => (1 : ℂ))) ∧
    (∀ a b : Fin n, a < b → ε a = ε b →
      ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) *ᵥ
        (fun _ : Unit => (1 : ℂ)) = 0) ∧
    (fun _ : Unit => (1 : ℂ)) ≠ 0 ∧
    Formalism.REAL.KHighest ε (kunits (trivialKType ε)) 0 (trivialKType ε).w ∧ (trivialKType ε).w ≠ 0 := by sorry
