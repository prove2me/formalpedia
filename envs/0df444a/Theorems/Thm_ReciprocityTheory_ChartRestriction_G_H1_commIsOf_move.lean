-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_commIsOf_move
-- name    : ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:12.058799+00:00
-- url     : https://prove2.me/theorems/525f6060-691e-4e52-a9c5-910574c25c79
-- title:
--   H1: comm Is Of move
-- statement:
--   The H1 construction uses the comm Is Of move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L119-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L119-L180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (k : ℤ)
    (θx₀ θy₀ : ThetaGrp G L₀ k T₀) (θx θy : ThetaGrp A L₁ k T)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : PMaps w ![(snd T A).left, (translPt A θx.pt).left] ![(snd T₀ G).left, (translPt G θx₀.pt).left] ![k, -k]
      θx.φ θx₀.φ (psiO hp τ hτ).left)
    (my : PMaps w ![(snd T A).left, (translPt A θy.pt).left] ![(snd T₀ G).left, (translPt G θy₀.pt).left] ![k, -k]
      θy.φ θy₀.φ (psiO hp τ hτ).left)
    (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c)
    (H : CommIsOf G L₀ k θx₀ θy₀ c₀) : CommIsOf A L₁ k θx θy c := by sorry
