-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_appLE_res
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.appLE_res
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:54.490461+00:00
-- url     : https://prove2.me/theorems/2ce08d8d-649b-52b1-a447-4faaa45638f6
-- title:
--   Gt BCPf: app LE res
-- statement:
--   The Gt BCPf construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/CmapComp.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/CmapComp.lean#L34-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_CmapComp
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.appLE_res {X Y : Scheme.{0}} (g : Y ⟶ X) {U U₀ : X.Opens} (hU : U ≤ U₀) {V W : Y.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U₀) (hVW : V ≤ W) (u : Γ(X, U₀)ˣ) :
    (res hVW (res hW (pullU g U₀ u))).val = (g.appLE U V hV).hom (res hU u).val := by sorry
