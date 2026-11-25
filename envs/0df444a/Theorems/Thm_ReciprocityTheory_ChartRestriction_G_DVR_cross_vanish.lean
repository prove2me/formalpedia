-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cross_vanish
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.cross_vanish
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:21.455836+00:00
-- url     : https://prove2.me/theorems/6b7d0fd1-efba-4767-957a-017ee3399afb
-- title:
--   DVR: cross vanish
-- statement:
--   The DVR construction uses the cross vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L113-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L113-L482

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
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
set_option maxHeartbeats 4000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.cross_vanish (hL4 : Laws4) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (k N : ℕ) (e : ℕ)
    (X : letI := H.starRing; LB.Gen (LB.LinComb P.D.toPre.P.L
      ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]))
    (hX : X.IsGen)
    (uR : letI := H.starRing; LB.Gen (LB.LinComb P.D.toPre.P.L
      (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (huR0 : LB.Gen.Corr P.D.toPre.P.L _ _ _ _
      (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L))
    (hinj : letI := H.starRing; Function.Injective fun χ : P.D.toPre.X => star a • χ)
    (σ'' : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (τ : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))))
    (f'' : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α)
    (f : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α)
    (h'' : ∀ i, P.U.ExpandsAt e (k * N) (σ'' i) (f'' i))
    (hf : ∀ i, P.U.ExpandsAt e k (τ i) (f i))
    (hrel : letI := H.starRing; ∀ i χ, ∃ u : LB.Gen (LB.LinComb P.D.toPre.P.L (pullφB P.oD a χ) (pullε k N)),
      u.IsGen ∧
      LB.Gen.Corr P.D.toPre.P.L _ _ _ _ u (LB.mulGen P.D.toPre.P.L _ _ _ _ X
        (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left)) ∧
      GeneratorPullback.SecRel P.D.toPre.P.L (DegPre.famφB P.D.toPre (star a • χ)) (DegPre.famε (k * N))
        (f'' i (star a • χ)) (DegPre.famφB P.D.toPre χ) (DegPre.famε k) (f i χ) (P.oD.onB.act a).left
        (pullφB P.oD a χ) (pullε k N) u)
    (hoff : letI := H.starRing; ∀ i β, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' i β).f j = 0) :
    ∀ j, ((fstG (maximalIdeal V) e t.G).left.app _).hom
      ((subSec
        (mulSec P.U.LG.L _ _ _ _ (σ'' 0) (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left))
        (mulSec P.U.LG.L _ _ _ _ (σ'' 1) (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left))).f j) = 0 := by sorry
