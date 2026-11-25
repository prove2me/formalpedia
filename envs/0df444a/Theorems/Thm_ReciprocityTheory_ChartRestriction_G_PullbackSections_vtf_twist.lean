-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_twist
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_twist
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:44.743126+00:00
-- url     : https://prove2.me/theorems/fc615a1c-4cca-4840-afdc-bd3919255caa
-- title:
--   Pullback Sections: vtf twist
-- statement:
--   The Pullback Sections construction uses the vtf twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L133-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtFrRdA.lean#L133-L157

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_twist {a b : ℤ} {ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A} {m : Over.mk x0 ⊗ A ⟶ A}
    {hm : ψ ≫ snd (Over.mk x0) A = m}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b (Over.mk x0))} {s' : LB.Sec (LPow A L a (Over.mk x0))}
    (h : IsTwistPull A L ψ m hm a b α s s') (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (j : Fin 2 → L.ι)
    (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) :
    valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0)) =
      valAt' p _ (α.s j).val *
        valAt' (p ≫ ψ.left) ((LPow A L b (Over.mk x0)).U (fun _ => j 1)) (s.f (fun _ => j 1)) := by sorry
