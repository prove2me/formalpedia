-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_xphi_linInd
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.xphi_linInd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:21:20.51415+00:00
-- url     : https://prove2.me/theorems/b11974ca-71db-4a12-b3bf-29f4a6370f74
-- title:
--   Hermitian Lift Identities: xphi lin Ind
-- statement:
--   The Hermitian Lift Identities construction uses the xphi lin Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L46-L51

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by sorry
