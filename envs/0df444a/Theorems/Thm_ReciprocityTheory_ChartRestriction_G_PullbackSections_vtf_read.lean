-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_read
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_read
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:22.55803+00:00
-- url     : https://prove2.me/theorems/813980a9-afa8-5695-bb11-4adc8367d28a
-- title:
--   Pullback Sections: vtf read
-- statement:
--   The Pullback Sections construction uses the vtf read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L110-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L110-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_read {k : ℤ} (F : LB.Sec (LPow A L k (Over.mk x0))) (a : Over.mk x0 ⟶ A) (fr : L.ι → ℂ)
    (hfr : ∀ j j', ⊤ ≤ a.left ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j = valAt' a.left _ (L.g j j' : Γ(A.left, L.U j ⊓ L.U j')) * fr j')
    (j j' : L.ι) (hj : ⊤ ≤ a.left ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ a.left ⁻¹ᵁ L.U j') (θ : ℂ)
    (h : valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ * fr j ^ k) :
    valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j')) (F.f (fun _ => j')) = θ * fr j' ^ k := by sorry
