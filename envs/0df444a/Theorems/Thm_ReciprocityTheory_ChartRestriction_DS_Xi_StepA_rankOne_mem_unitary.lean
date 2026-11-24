-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOne_mem_unitary
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOne_mem_unitary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:25:17.780423+00:00
-- url     : https://prove2.me/theorems/d999ed30-4f54-4e93-b817-7a72ca04a83b
-- title:
--   Step A: rank One mem unitary
-- statement:
--   The Step A construction uses the rank One mem unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L84-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOne_mem_unitary {k r' : ℕ} (hOSM : OneStepMem) {c : ℂ} (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by sorry
