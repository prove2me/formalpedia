-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobCong
-- name    : ReciprocityTheory.ChartRestriction.L1.frobCong
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:18:51.862956+00:00
-- url     : https://prove2.me/theorems/915ec925-cd1e-5aaa-a4bb-42e42b3f13a1
-- title:
--   L1: frob Cong
-- statement:
--   The L1 construction uses the frob Cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobCong.lean#L32-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFrobCong.lean#L32-L70

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

theorem ReciprocityTheory.ChartRestriction.L1.frobCong {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hA : LiesAbove A v) (hp : (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal)).Prime)
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    x ^ Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) - x ∈ A.nonunits := by sorry
