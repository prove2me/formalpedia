-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_conjH_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.CB.conjH_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:16.935879+00:00
-- url     : https://prove2.me/theorems/b4a4a5a2-6dfc-48a7-b29a-4f973e1c04e9
-- title:
--   CB: conj H mul
-- statement:
--   The CB construction uses the conj H mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L46-L49

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.CB.conjH_mul (a b : Mat k r) :
    Hpk k r * a * Hpk k r * (Hpk k r * b * Hpk k r) = Hpk k r * (a * b) * Hpk k r := by sorry
