-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secRel_pullSecs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.secRel_pullSecs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:48.058983+00:00
-- url     : https://prove2.me/theorems/717cbb72-5709-51d9-999f-5a1850c73d92
-- title:
--   DVR: sec Rel pull Secs
-- statement:
--   The DVR construction uses the sec Rel pull Secs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L501-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L501-L539

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_transport

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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
variable {D F}

theorem ReciprocityTheory.ChartRestriction.G.DVR.secRel_pullSecs (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k) (χ : D.toPre.X) :
    ∀ (χ₀ : D.toPre.X) (hβ : star a • χ₀ = star a • χ), χ₀ = χ →
      GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N))
        (Classical.choose (sec_transport hL (pullProd_sameSum D F oa a N k χ₀ (star a • χ) hβ)
          (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s χ₀)))
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left
        (pullφ D F oa a χ) (pullε k N) (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ) := by sorry
