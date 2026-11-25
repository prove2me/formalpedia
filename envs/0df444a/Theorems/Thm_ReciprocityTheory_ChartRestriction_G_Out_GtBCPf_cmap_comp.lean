-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_cmap_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.cmap_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:12.462035+00:00
-- url     : https://prove2.me/theorems/cda643bc-7478-4592-ae37-ed18db45ddde
-- title:
--   Gt BCPf: cmap comp
-- statement:
--   The Gt BCPf construction uses the cmap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/CmapComp.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/CmapComp.lean#L16-L31

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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.cmap_comp {κ X A A' : Type} [AddCommGroup X] [CommRing A] [CommRing A']
    (b : Module.Basis κ ℤ X) (ρ : A →+* A') (v : κ → Aˣ) (v' : κ → A'ˣ)
    (hv : ∀ k, (v' k).val = ρ (v k).val) (x : Multiplicative X) :
    cmap b v' x = ρ (cmap b v x) := by sorry
