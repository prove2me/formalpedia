-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_yx
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_yx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:27:59.208813+00:00
-- url     : https://prove2.me/theorems/eecc1ab4-2936-436c-9eef-03b35b58ec6b
-- title:
--   Step A: ea yx
-- statement:
--   The Step A construction uses the ea yx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L538-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L538-L540

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) :
    Yx k r' x a = ((heis0 k r' x)⁻¹ * w0 k r' 1) *ᵥ phiV' k (1 + r') a := by sorry
