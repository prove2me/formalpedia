-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_rmul_int
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.rmul_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:47.382254+00:00
-- url     : https://prove2.me/theorems/bac5d139-0bb9-410e-b6fa-c14623dd58c9
-- title:
--   Hermitian Lift Identities: rmul int
-- statement:
--   The Hermitian Lift Identities construction uses the rmul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L122-L126

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by sorry
