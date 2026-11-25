-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_bdd_comp_pt
-- name    : ReciprocityTheory.ChartRestriction.L1.bdd_comp_pt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:51.312028+00:00
-- url     : https://prove2.me/theorems/dd4be1e3-995c-4a6a-81f2-4667cc7af465
-- title:
--   L1: bdd comp pt
-- statement:
--   The L1 construction uses the bdd comp pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGmForm.lean#L66-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
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

theorem ReciprocityTheory.ChartRestriction.L1.bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (fun τ => f (pt a b e τ)) := by sorry
