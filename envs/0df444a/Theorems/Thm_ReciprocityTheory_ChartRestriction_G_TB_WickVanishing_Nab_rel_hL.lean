-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_rel_hL
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.rel_hL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:45:04.596791+00:00
-- url     : https://prove2.me/theorems/49085844-3813-5077-927b-60cfec6f3709
-- title:
--   Nab: rel h L
-- statement:
--   The Nab construction uses the rel h L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SigCancel.lean#L149-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SigCancel.lean#L149-L200

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.rel_hL {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (u : Fin d → k) (hu : ∀ j, ∃ r, algebraMap R k r = u j) :
    Dof (B.FK k) u (B.hL k h w0) + ∑ c, sgOf k h c * C (u c) ∈ Ig R k (Fin 1 × Fin d) := by sorry
