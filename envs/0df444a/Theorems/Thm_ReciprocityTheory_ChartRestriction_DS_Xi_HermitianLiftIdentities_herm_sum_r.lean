-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_sum_r
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.herm_sum_r
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:25.220212+00:00
-- url     : https://prove2.me/theorems/f5651f1e-7060-5187-9ffb-87181f1816c4
-- title:
--   Hermitian Lift Identities: herm sum r
-- statement:
--   The Hermitian Lift Identities construction uses the herm sum r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L32-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.herm_sum_r {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by sorry
