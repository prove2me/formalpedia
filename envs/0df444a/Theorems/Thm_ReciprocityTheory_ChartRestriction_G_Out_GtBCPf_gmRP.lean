-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_gmRP
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gmRP
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:45.662442+00:00
-- url     : https://prove2.me/theorems/17d9322a-04c3-53e6-8f0d-382fc277f38f
-- title:
--   Gt BCPf: gm RP
-- statement:
--   The Gt BCPf construction uses the gm RP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L20-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gmRP {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U)
    (hz : z ∈ V) (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u := by sorry
