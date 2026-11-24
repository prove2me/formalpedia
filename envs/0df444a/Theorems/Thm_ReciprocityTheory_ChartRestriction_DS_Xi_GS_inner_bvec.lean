-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_inner_bvec
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.inner_bvec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:15.402404+00:00
-- url     : https://prove2.me/theorems/b01eb4ef-00fa-44c6-bcde-bce38ada7a6c
-- title:
--   GS: inner bvec
-- statement:
--   The GS construction uses the inner bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExistsKmat.lean#L108-L113

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.inner_bvec (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by sorry
