-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_NuGe_smul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.NuGe.smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T06:23:12.579791+00:00
-- url     : https://prove2.me/theorems/da97aff4-9919-54ef-b4af-851dc6bed4f6
-- title:
--   Nu Ge: smul
-- statement:
--   The Nu Ge construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ConstBFMul.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ConstBFMul.lean#L80-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ConstBFMul
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
variable (Q : D.toPre.X → ℤ)

theorem ReciprocityTheory.ChartRestriction.G.DVR.NuGe.smul {k : ℕ} {s s' : Fam D.toPre F k} {r q : ℚ} {ζ : F}
    (hq : ((q : ℚ) : WithTop ℚ) ≤ v ζ) (hs : Fam.IsSmul D.toPre F ζ s s') (h : NuGe D Q F v k s r) :
    NuGe D Q F v k s' (r + q) := by sorry
