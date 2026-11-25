-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_gN_right
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.CB.gN_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:58.921896+00:00
-- url     : https://prove2.me/theorems/7b072d6b-f6cf-4e3d-98bb-1e968b72b3d5
-- title:
--   CB: g N right
-- statement:
--   The CB construction uses the g N right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L40-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
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
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.CB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.CB.gN_right {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (g * κ) = gN g := by sorry
