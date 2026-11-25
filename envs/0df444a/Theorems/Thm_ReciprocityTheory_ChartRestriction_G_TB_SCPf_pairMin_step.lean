-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_pairMin_step
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.pairMin_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:11.936599+00:00
-- url     : https://prove2.me/theorems/30c30fbd-09ac-5816-a3fb-a5ad8b33f71e
-- title:
--   SCPf: pair Min step
-- statement:
--   The SCPf construction uses the pair Min step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L75-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondOrderIterateEqZero.lean#L75-L99

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

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.pairMin_step (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) (l l' : ι) (hc : c l = c l')
    (hs : s l = true) (hs' : s l' = false) :
    pairMin c s (n + Finsupp.single l 1 + Finsupp.single l' 1) = pairMin c s n + 1 := by sorry
