-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_pe_iso
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_iso
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:26.788266+00:00
-- url     : https://prove2.me/theorems/f23498d9-abd1-4f11-bfc5-ce3cc56f98ac
-- title:
--   GS: pe iso
-- statement:
--   The GS construction uses the pe iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L22-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_iso (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by sorry
