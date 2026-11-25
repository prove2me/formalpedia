-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_ga_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:59.790961+00:00
-- url     : https://prove2.me/theorems/f1e5b5a4-37a4-5ae9-9230-dc55c099a659
-- title:
--   Step A: ea ga zero
-- statement:
--   The Step A construction uses the ea ga zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/StarLastDotLast.lean#L21-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_zero {k r : ℕ} (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : Ga k r 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by sorry
