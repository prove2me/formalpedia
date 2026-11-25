-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_secondOrder_iterate_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_iterate_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:19.157049+00:00
-- url     : https://prove2.me/theorems/849217b6-ca0d-522d-bce2-043d4c4f3a5a
-- title:
--   SCPf: second Order iterate eq zero
-- statement:
--   The SCPf construction uses the second Order iterate eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L126-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L126-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
variable {π : Type} [Fintype π] [DecidableEq π]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_iterate_eq_zero (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (P : MvPolynomial ι k) (e : ℕ)
    (hP : ∀ n ∈ P.support, pairMin c s n ≤ e) (j : ℕ) (hj : e < j) :
    (secondOrder k κ)^[j] P = 0 := by sorry
