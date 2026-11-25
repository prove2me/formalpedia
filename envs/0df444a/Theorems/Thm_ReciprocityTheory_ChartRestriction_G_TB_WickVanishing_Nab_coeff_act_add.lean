-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_coeff_act_add
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_act_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:30.714641+00:00
-- url     : https://prove2.me/theorems/69112286-d606-4f92-a1b3-561bfc069e32
-- title:
--   Nab: coeff act add
-- statement:
--   The Nab construction uses the coeff act add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L26-L34

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_act_add (B : FB R d O) (a b : O) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act (a + b) i) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act b i) := by sorry
