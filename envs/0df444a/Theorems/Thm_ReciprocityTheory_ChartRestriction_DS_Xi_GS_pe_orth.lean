-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_pe_orth
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_orth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:01.709632+00:00
-- url     : https://prove2.me/theorems/ad0bba78-a90e-44ad-a6c3-0b7e848a513d
-- title:
--   GS: pe orth
-- statement:
--   The GS construction uses the pe orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ProdIicCastLE.lean#L17-L20

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by sorry
