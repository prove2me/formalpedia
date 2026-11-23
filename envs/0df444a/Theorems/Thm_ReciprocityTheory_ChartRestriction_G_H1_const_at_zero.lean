-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_const_at_zero
-- name    : ReciprocityTheory.ChartRestriction.G.H1.const_at_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:43.880331+00:00
-- url     : https://prove2.me/theorems/283e9c8e-bfa8-4155-859f-3091e517a0c2
-- title:
--   H1: const at zero
-- statement:
--   The H1 construction uses the const at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L122-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L122-L177

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.H1.const_at_zero (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (u : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)))
    (hu : ∀ α, (u α).IsGen)
    (hc : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u α) (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w))
    (v : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α p.y) (DegPre.deltaε k)))
    (hcv : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (v α) (DegPre.zF D F).left)
      (DegPre.famMult D F k p.y α))
    (α : D.X) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, val (u (α + i • p.y))
        ((DegPre.zF D F).left ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) *
        (val (v α) (DegPre.zF D F).left z J)⁻¹ =
      (∏ i ∈ Finset.range k, hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ := by sorry
