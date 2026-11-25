-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_top_eqOn
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.top_eqOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:32.503273+00:00
-- url     : https://prove2.me/theorems/86408322-a7d4-59cd-a932-e03ee9ec670b
-- title:
--   Cap Phi: top eq On
-- statement:
--   The Cap Phi construction uses the top eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L121-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.top_eqOn (x : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (h : Set.EqOn F G (OmegaSet n)) :
    Set.EqOn (Formalism.QuantumDeterminants.Top negL x a b F) ((capEntry negE x a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (OmegaSet n) := by sorry
