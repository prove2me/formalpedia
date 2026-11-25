-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_hL
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_hL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:33.888791+00:00
-- url     : https://prove2.me/theorems/45d02edd-fe73-41f2-940c-b0cb30366796
-- title:
--   Nab: dof h L
-- statement:
--   The Nab construction uses the dof h L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SigCancel.lean#L54-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SigCancel.lean#L54-L119

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_hL (B : FB R d O) (h : PS k 2 d) (w0 : O) (u : Fin d → k) :
    Dof (B.FK k) u (ev (n := 1) ![pt k d 0, B.actK k w0] h) =
      ∑ b, C (u b) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) +
        ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) := by sorry
