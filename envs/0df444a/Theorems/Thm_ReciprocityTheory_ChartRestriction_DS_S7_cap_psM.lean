-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cap_psM
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cap_psM
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:52.715322+00:00
-- url     : https://prove2.me/theorems/9c71b1e6-fd9c-5917-bf36-43949d59f339
-- title:
--   S7: cap ps M
-- statement:
--   The S7 construction uses the cap ps M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L190-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L190-L227

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open CapPs

theorem ReciprocityTheory.ChartRestriction.DS.S7.cap_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ (Y : ℂ), ∀ z ∈ U,
        Formalism.QuantumDeterminants.qdetOp negL (Y + ((n : ℂ) - 1) / 2) (psM T μ) z =
          Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • psM T μ z := by sorry
