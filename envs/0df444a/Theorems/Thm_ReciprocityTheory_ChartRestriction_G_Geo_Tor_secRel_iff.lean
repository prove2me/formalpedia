-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:48.495833+00:00
-- url     : https://prove2.me/theorems/cedf8159-c471-45d8-b702-91b6c7351f9b
-- title:
--   Tor: sec Rel iff
-- statement:
--   The Tor construction uses the sec Rel iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L336-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L336-L373

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff (hL : L.IsLB) {K₃ : Type} [Fintype K₃] (φ₁ : K' → (Y' ⟶ X)) (ε₁ : K' → ℤ)
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃)) :
    (Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s₁ r z J = sval s (r ≫ h) z J * (val u r z J).val) ∧
    ((∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = sval s (𝟙 Y' ≫ h) y J * (val u (𝟙 Y') y J).val) →
      Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u) := by sorry
