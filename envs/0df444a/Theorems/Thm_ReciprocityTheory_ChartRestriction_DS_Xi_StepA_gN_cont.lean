-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_gN_cont
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.gN_cont
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:10:07.805804+00:00
-- url     : https://prove2.me/theorems/5bfd1427-2848-4445-986d-c1f6f10d0601
-- title:
--   Step A: g N cont
-- statement:
--   The Step A construction uses the g N cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RankOneLeviComm.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RankOneLeviComm.lean#L107-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by sorry
