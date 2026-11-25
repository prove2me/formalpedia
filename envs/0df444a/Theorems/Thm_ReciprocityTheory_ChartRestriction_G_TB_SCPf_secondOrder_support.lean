-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_secondOrder_support
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_support
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:04.889382+00:00
-- url     : https://prove2.me/theorems/e962a276-4bbd-54fa-95f4-a29ee45c8a0f
-- title:
--   SCPf: second Order support
-- statement:
--   The SCPf construction uses the second Order support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L101-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L101-L124

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

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_support (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (Q : MvPolynomial ι k) (p j : ℕ)
    (hQ : ∀ n ∈ Q.support, pairMin c s n + j ≤ p) :
    ∀ n ∈ (secondOrder k κ Q).support, pairMin c s n + (j + 1) ≤ p := by sorry
