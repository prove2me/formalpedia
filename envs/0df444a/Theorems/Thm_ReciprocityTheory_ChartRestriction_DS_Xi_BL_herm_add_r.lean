-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_add_r
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_add_r
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:20.510811+00:00
-- url     : https://prove2.me/theorems/df830625-f87c-4801-b44b-d18bd46e82ee
-- title:
--   BL: herm add r
-- statement:
--   The BL construction uses the herm add r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L37-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (v w w' : Fin n → ℂ) :
    herm H v (w + w') = herm H v w + herm H v w' := by sorry
