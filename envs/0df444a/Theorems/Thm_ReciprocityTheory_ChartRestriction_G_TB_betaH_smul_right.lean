-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_betaH_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.TB.betaH_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:55.962775+00:00
-- url     : https://prove2.me/theorems/70dec329-01c9-484e-bdd3-d2b5eb63f8df
-- title:
--   TB: beta H smul right
-- statement:
--   The TB construction uses the beta H smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EigenLift.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EigenLift.lean#L27-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ReciprocityTheory.ChartRestriction.G.TB.betaH_smul_right {k : Type} [CommRing k] {d : ℕ} (c : k) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ (c • η) = c * betaH k ξ η := by sorry
