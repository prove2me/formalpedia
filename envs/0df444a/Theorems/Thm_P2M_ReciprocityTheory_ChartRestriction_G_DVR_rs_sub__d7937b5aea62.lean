-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_sub__d7937b5aea62
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_sub__d7937b5aea62
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:07.45686+00:00
-- url     : https://prove2.me/theorems/ad4bcaef-e782-4c85-bad0-53b662e64f22
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR rs sub  d7937b5aea62: P2 M Reciprocity Theory Chart Restriction G DVR rs sub  d7937b5aea62
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR rs sub  d7937b5aea62 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR rs sub  d7937b5aea62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L109-L109

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_sub__d7937b5aea62 {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) : rs h (x - y) = rs h x - rs h y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«rs_sub'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_sub__d7937b5aea62
