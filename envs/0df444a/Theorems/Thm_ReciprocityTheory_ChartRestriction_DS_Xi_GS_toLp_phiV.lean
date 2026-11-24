-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_toLp_phiV
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.toLp_phiV
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:55:25.651801+00:00
-- url     : https://prove2.me/theorems/781f934a-a1dc-4104-bfed-8a395e41fad8
-- title:
--   GS: to Lp phi V
-- statement:
--   The GS construction uses the to Lp phi V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L132-L138

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.toLp_phiV (a : Fin (r + 1)) : (WithLp.toLp 2 (phiV k r a) : EE k r) =
    if a.val < r then WithLp.toLp 2 (bvec ⟨2 * r + k - a.val, by omega⟩) else
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 (bvec ⟨r, by omega⟩) + WithLp.toLp 2 (bvec ⟨r + k, by omega⟩)) := by sorry
