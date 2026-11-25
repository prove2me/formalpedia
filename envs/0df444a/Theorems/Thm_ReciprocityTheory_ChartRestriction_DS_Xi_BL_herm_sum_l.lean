-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_sum_l
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_sum_l
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:04.733647+00:00
-- url     : https://prove2.me/theorems/ad2cf234-8ee7-576e-bd5e-6198122904d1
-- title:
--   BL: herm sum l
-- statement:
--   The BL construction uses the herm sum l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L45-L47

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_sum_l (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by sorry
