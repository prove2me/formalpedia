-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sum_castLE
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_castLE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:41.864435+00:00
-- url     : https://prove2.me/theorems/bb8a0328-c576-4fad-819c-4fe23201da26
-- title:
--   BL: sum cast LE
-- statement:
--   The BL construction uses the sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L177-L183

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_castLE {M : Type} [AddCommMonoid M] {n l : ℕ} (h : l + 1 ≤ n) (f : Fin n → M)
    (hf : ∀ b : Fin n, l < b.val → f b = 0) : ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by sorry
