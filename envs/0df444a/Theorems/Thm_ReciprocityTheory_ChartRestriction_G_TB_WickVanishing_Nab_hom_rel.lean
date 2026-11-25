-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_hom_rel
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.hom_rel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:50.261331+00:00
-- url     : https://prove2.me/theorems/c7884e99-0768-5333-9f20-dc24c7952d6d
-- title:
--   Nab: hom rel
-- statement:
--   The Nab construction uses the hom rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L91-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L91-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.hom_rel (B : FB R d O) (a : O) (c b : Fin d) :
    ∑ j, pderiv k ((0 : Fin 1), j) (B.actK k a c) * Jac (lawK k B) j b =
      ∑ j, ev (n := 1) ![B.actK k a] (Jac (lawK k B) c j) * C (dAct k B a j b) := by sorry
