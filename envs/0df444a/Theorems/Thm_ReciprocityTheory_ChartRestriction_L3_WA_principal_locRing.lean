-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_principal_locRing
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.principal_locRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:18.69324+00:00
-- url     : https://prove2.me/theorems/6ff5695a-2152-4266-93b2-eab298e4257d
-- title:
--   WA: principal loc Ring
-- statement:
--   The WA construction uses the principal loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/IsHermSemilocalLocRing.lean#L68-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/IsHermSemilocalLocRing.lean#L68-L125

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem ReciprocityTheory.ChartRestriction.L3.WA.principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by sorry
