-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.dof_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:38.341537+00:00
-- url     : https://prove2.me/theorems/03f8a2a7-05b6-4a29-958a-7ed2e8ae1632
-- title:
--   GE: dof C mul
-- statement:
--   The GE construction uses the dof C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofDApply.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofDApply.lean#L46-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.dof_C_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by sorry
