-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_ofReal_fsR
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.ofReal_fsR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:01:17.316921+00:00
-- url     : https://prove2.me/theorems/1205df67-ba4f-5712-a6ef-af2d83b607c2
-- title:
--   Hermitian Lift Identities: of Real fs R
-- statement:
--   The Hermitian Lift Identities construction uses the of Real fs R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L26-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by sorry
