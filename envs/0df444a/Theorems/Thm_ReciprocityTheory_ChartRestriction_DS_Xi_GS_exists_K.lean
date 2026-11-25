-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_exists_K
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.exists_K
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:43.042281+00:00
-- url     : https://prove2.me/theorems/02685049-71eb-4bee-8e86-2e2d6cfdfaa2
-- title:
--   GS: exists K
-- statement:
--   The GS construction uses the exists K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L13-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L13-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.exists_K (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by sorry
