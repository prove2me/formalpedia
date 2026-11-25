-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_natCard_mem
-- name    : ReciprocityTheory.ChartRestriction.L1.natCard_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:03.485887+00:00
-- url     : https://prove2.me/theorems/0fe06b16-72c9-4a2e-80d7-9475c4475e73
-- title:
--   L1: nat Card mem
-- statement:
--   The L1 construction uses the nat Card mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobCong.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobCong.lean#L19-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
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

theorem ReciprocityTheory.ChartRestriction.L1.natCard_mem {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 E)} (h : LiesAbove A v) :
    ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : Ω) ∈ A.nonunits := by sorry
