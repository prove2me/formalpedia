-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_entry_le_gN
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.DetB.entry_le_gN
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:53:55.859969+00:00
-- url     : https://prove2.me/theorems/059b8797-40e4-422d-b4f9-d33019360050
-- title:
--   Det B: entry le g N
-- statement:
--   The Det B construction uses the entry le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianLiftIdentities.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianLiftIdentities.lean#L12-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.DetB.entry_le_gN {k r : ℕ} (h : Mat k r) (m j : Fin (2 * r + k + 1)) : ‖h m j‖ ≤ gN h := by sorry
