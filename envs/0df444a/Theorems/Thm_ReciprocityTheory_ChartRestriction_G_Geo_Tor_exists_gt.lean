-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:24.2519+00:00
-- url     : https://prove2.me/theorems/09fae3ac-1715-4242-8816-0288f90c50ca
-- title:
--   Tor: exists gt
-- statement:
--   The Tor construction uses the exists gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsZeroGt.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsZeroGt.lean#L42-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gt (b : TF (R := R) F ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → ((TF (R := R) F).left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφ D F b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (v χ) (𝟙 _) y J := by sorry
