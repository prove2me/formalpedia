-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_phi
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gen_phi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:18.269502+00:00
-- url     : https://prove2.me/theorems/42ba3ed9-57af-4001-af2a-317481aac6db
-- title:
--   DVR: gen phi
-- statement:
--   The DVR construction uses the gen phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L266-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L266-L281

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F}

theorem ReciprocityTheory.ChartRestriction.G.DVR.gen_phi (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w)) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J := by sorry
