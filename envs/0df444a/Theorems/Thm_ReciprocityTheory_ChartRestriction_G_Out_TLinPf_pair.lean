-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_pair
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.pair
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:50.101884+00:00
-- url     : https://prove2.me/theorems/e33ad4d8-0fff-4b30-ab00-d7789dade44f
-- title:
--   TLin Pf: pair
-- statement:
--   The TLin Pf construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/Imports.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/Imports.lean#L28-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_Imports
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
include hO

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.pair (hu : u.IsGen) : ∃ ρ : Γ((thickObj R I e G).left, ⊤)ˣ,
    ∀ (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι),
      LB.Coh D.toPre.P.L (φA U ιD e a χ) jA → LB.Coh D.toPre.P.L (φB U ιG e a χ) jB →
      (∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k') →
      res (inf_le_right : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓
          LB.wchart D.toPre.P.L (φA U ιD e a χ) jA ≤ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
          ((lhs U ιD e a χ u).s jA) =
        res le_top ρ * res inf_le_left ((rhs U ιG e a χ).s jB) := by sorry
