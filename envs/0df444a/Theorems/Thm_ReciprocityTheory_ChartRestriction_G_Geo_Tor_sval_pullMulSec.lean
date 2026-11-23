-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_pullMulSec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:32.958803+00:00
-- url     : https://prove2.me/theorems/6fab433a-7065-4352-954f-c1b8d4886811
-- title:
--   Tor: sval pull Mul Sec
-- statement:
--   The Tor construction uses the sval pull Mul Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L323-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean#L323-L334

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.sval_pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (r : Z ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullMulSec s h u hu) r z J = sval s (r ≫ h) z J * (val u r z J).val := by sorry
