-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_norm_bd
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.CB.norm_bd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:29:50.423941+00:00
-- url     : https://prove2.me/theorems/59626aa7-a953-59e3-acd5-a941b265a9ba
-- title:
--   CB: norm bd
-- statement:
--   The CB construction uses the norm bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XiRNonneg.lean#L75-L84

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.CB.norm_bd {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h : Mat k r) (hh : h ∈ GV k r) :
    ‖F h‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (gN h ^ (-A)) := by sorry
