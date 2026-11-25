-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_iter
-- name    : ReciprocityTheory.ChartRestriction.G.H1.iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:38.901495+00:00
-- url     : https://prove2.me/theorems/f90e3274-cd7a-4a1c-b412-9e1d6272b6a8
-- title:
--   H1: iter
-- statement:
--   The H1 construction uses the iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L90-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L90-L120

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

theorem ReciprocityTheory.ChartRestriction.G.H1.iter {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (u : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)))
    (hu : ∀ α, (u α).IsGen)
    (hc : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u α) (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w))
    (ss : Fin (k + 1) → Fam D F k) (H : ∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) :
    ∀ (n : ℕ) (hn : n < k + 1) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J →
      sval ((ss ⟨n, hn⟩).s (α + n • p.y)) r z J = sval ((ss 0).s α) (r ≫ (DegPre.trPt D F (p.g.b ^ n)).left) z J *
        (∏ i ∈ Finset.range n, val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (n - 1 - i))).left) z J).val := by sorry
