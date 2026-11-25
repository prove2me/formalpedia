-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:11.585323+00:00
-- url     : https://prove2.me/theorems/ea58f7da-e995-5cf0-8f5d-21062999f6a0
-- title:
--   Step A: Dl conj
-- statement:
--   The Step A construction uses the Dl conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L217-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L217-L282

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_conj (l : Fin (r + 1)) (Y n n' : Mat k r) (hn : n ∈ GV k r) (α β : Fin (r + 1) → ℂ)
    (hα : α 0 = 0) (hβ : β 0 = 0)
    (hn' : ∀ b, n' *ᵥ phiV' k r b = phiV' k r b - α b • phiV' k r 0)
    (hnn : ∀ a, n *ᵥ phiV' k r a = phiV' k r a - β a • phiV' k r 0) :
    Dl k r l (n⁻¹ * Y * n') = Dl k r l Y := by sorry
