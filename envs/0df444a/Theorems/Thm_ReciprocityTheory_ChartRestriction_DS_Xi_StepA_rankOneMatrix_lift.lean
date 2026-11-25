-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOneMatrix_lift
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOneMatrix_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:56:34.459794+00:00
-- url     : https://prove2.me/theorems/a89d1ea6-d62b-423b-b1c3-eb5ec852625e
-- title:
--   Step A: rank One Matrix lift
-- statement:
--   The Step A construction uses the rank One Matrix lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L169-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L169-L197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOneMatrix_lift (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : w0 k r' c *ᵥ liftVec k 1 r' v = liftVec k 1 r' v := by sorry
