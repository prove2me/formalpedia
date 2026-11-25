-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Gm_smul
-- name    : ReciprocityTheory.ChartRestriction.L1.Gm_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:42.276813+00:00
-- url     : https://prove2.me/theorems/1699c3f9-1e6c-5721-9b2c-86ea9091a8f7
-- title:
--   L1: Gm smul
-- statement:
--   The L1 construction uses the Gm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmSlash.lean#L13-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmSlash.lean#L13-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by sorry
