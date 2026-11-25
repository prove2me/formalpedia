-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_fsE_left
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:49.283208+00:00
-- url     : https://prove2.me/theorems/8b9bf0f7-c9d5-5e80-8ffb-1bf3f53bed33
-- title:
--   Hermitian Lift Identities: fs E left
-- statement:
--   The Hermitian Lift Identities construction uses the fs E left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L61-L67

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by sorry
