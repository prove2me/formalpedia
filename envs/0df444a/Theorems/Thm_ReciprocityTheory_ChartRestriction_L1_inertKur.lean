-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inertKur
-- name    : ReciprocityTheory.ChartRestriction.L1.inertKur
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:57.884683+00:00
-- url     : https://prove2.me/theorems/a2aa9e75-92d0-5da5-bef6-abe4dbd7d735
-- title:
--   L1: inert Kur
-- statement:
--   The L1 construction uses the inert Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModInertKur.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModInertKur.lean#L15-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModInertKur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.inertKur {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by sorry
