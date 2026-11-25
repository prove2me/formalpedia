-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_iw_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.iw_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:31.005354+00:00
-- url     : https://prove2.me/theorems/0391568e-b348-5ab4-84f8-1a8a70509b49
-- title:
--   BL: iw apply
-- statement:
--   The BL construction uses the iw apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L150-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L150-L171

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
variable (k n : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.iw_apply (hIW : IW) (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    ∃ κ : Mat k n, κ ∈ GV k n ∧ κᴴ * κ = 1 ∧ ∃ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, m *ᵥ phiV k n a = ∑ b, τ b a • (κ *ᵥ phiV k n b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k n l (fun a => m *ᵥ phiV k n a) := by sorry
