-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_tel_formal
-- name    : ReciprocityTheory.ChartRestriction.G.H1.tel_formal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:48.808687+00:00
-- url     : https://prove2.me/theorems/6b679bdf-3608-4526-a27b-9528ebcf650e
-- title:
--   H1: tel formal
-- statement:
--   The H1 construction uses the tel formal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L64-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PhiPow.lean#L64-L88

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

theorem ReciprocityTheory.ChartRestriction.G.H1.tel_formal {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) (hb : DegPre.trF D F y = DegPre.trPt D F (b ^ k))
    {U : Type} [CommGroup U] (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    (∏ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4,
        h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j) *
      ∏ j : Fin 4 ⊕ Fin 4, h (DegPre.deltaφ D F k α y j) ^ (-DegPre.deltaε k j) = 1 := by sorry
