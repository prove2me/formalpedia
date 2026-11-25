-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cross_to_K
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.cross_to_K
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:22.949831+00:00
-- url     : https://prove2.me/theorems/bdb74fc7-0a8b-4322-b80c-21c4150b9845
-- title:
--   DVR: cross to K
-- statement:
--   The DVR construction uses the cross to K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L312-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L312-L377

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}

theorem ReciprocityTheory.ChartRestriction.G.DVR.cross_to_K (LG : LB G.left) (hLG : LG.IsLB) (f : G ⟶ G) (k m : ℕ)
    (σ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (m : ℤ))))
    (τ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (s'' : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ))))
    (s : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))))
    (lam : Fin 2 → V) (hlam : ∀ i, lam i ≠ 0)
    (hσ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ)) (s'' i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (m : ℤ)) (σ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hτ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) (s i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (τ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hC : ∀ j, (mulSec LG _ _ _ _ (σ 0) (pullSec LG _ _ (τ 1) f.left)).f j =
      (mulSec LG _ _ _ _ (σ 1) (pullSec LG _ _ (τ 0) f.left)).f j) :
    ∀ j, (mulSec LG _ _ _ _ (s'' 0) (pullSec LG _ _ (s 1) (endK f))).f j =
      (mulSec LG _ _ _ _ (s'' 1) (pullSec LG _ _ (s 0) (endK f))).f j := by sorry
