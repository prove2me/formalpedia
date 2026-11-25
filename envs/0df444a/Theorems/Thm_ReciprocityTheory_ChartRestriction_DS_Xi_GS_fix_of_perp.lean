-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_fix_of_perp
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GS.fix_of_perp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:49:44.797982+00:00
-- url     : https://prove2.me/theorems/37258296-2a57-52bc-a6b9-088d885eaaf8
-- title:
--   GS: fix of perp
-- statement:
--   The GS construction uses the fix of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixOfPerp.lean#L67-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixOfPerp.lean#L67-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GS.fix_of_perp (c : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c)
    (hiso : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (x : EE k r)
    (hx1 : ∀ a, inner ℂ (c a) x = 0) (hx2 : ∀ a, inner ℂ (HE k r (c a)) x = 0) : HE k r x = x := by sorry
