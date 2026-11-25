-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_fsE_right
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:54.282414+00:00
-- url     : https://prove2.me/theorems/b7c4defc-e68b-549d-b995-c24dca686105
-- title:
--   Hermitian Lift Identities: fs E right
-- statement:
--   The Hermitian Lift Identities construction uses the fs E right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L69-L75

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by sorry
