-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_qdet_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.qdet_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:38.610372+00:00
-- url     : https://prove2.me/theorems/598a4788-6829-5876-8d84-c49c4a98ad76
-- title:
--   Cap Phi: qdet eq
-- statement:
--   The Cap Phi construction uses the qdet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L149-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L149-L159

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.qdet_eq (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL u F z = ((capelliC (negE (n := n)) u G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by sorry
