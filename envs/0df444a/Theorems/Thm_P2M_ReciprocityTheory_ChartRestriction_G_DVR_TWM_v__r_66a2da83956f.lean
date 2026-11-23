-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TWM_v__r_66a2da83956f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TWM_v__r_66a2da83956f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:55.740806+00:00
-- url     : https://prove2.me/theorems/ef759b53-da44-4490-a840-0dba029c723e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TWM v  r 66a2da83956f: P2 M Reciprocity Theory Chart Restriction G DVR TWM v  r 66a2da83956f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TWM v  r 66a2da83956f construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TWM v  r 66a2da83956f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TWMove.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TWMove.lean#L49-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TWM_v__r_66a2da83956f (r : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) : (0 : WithTop ℚ) ≤ v (ιr (v := v) r) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TWM».«v_ιr» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TWM_v__r_66a2da83956f
