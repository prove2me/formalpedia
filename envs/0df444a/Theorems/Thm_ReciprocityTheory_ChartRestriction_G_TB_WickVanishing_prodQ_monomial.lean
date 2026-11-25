-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_prodQ_monomial
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.prodQ_monomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:08:27.742334+00:00
-- url     : https://prove2.me/theorems/db14b572-24c1-4570-a63b-663726632c14
-- title:
--   Wick Vanishing: prod Q monomial
-- statement:
--   The Wick Vanishing construction uses the prod Q monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L94-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.prodQ_monomial (g : Fin n → (ι →₀ ℕ)) :
    prodQ (fun b => (monomial (g b) (1 : k) : MvPolynomial ι k)) = monomial (glue g) 1 := by sorry
