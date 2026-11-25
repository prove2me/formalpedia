-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_s_nonneg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.CB.s_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:30:42.638206+00:00
-- url     : https://prove2.me/theorems/0be40651-5b34-4929-995a-465b30a53203
-- title:
--   CB: s nonneg
-- statement:
--   The CB construction uses the s nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L109-L112

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.CB.s_nonneg (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (l : Fin (r + 1)) : 0 ≤ s l := by sorry
