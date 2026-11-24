-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_lipschitzConst_nonneg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.DetB.lipschitzConst_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:53:23.81397+00:00
-- url     : https://prove2.me/theorems/7ea190ff-5970-49ee-8b09-dbc84e375256
-- title:
--   Det B: lipschitz Const nonneg
-- statement:
--   The Det B construction uses the lipschitz Const nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianLiftIdentities.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianLiftIdentities.lean#L47-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.DetB.lipschitzConst_nonneg (k r : ℕ) : 0 ≤ K0 k r := by sorry
