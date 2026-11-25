-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_le_finset_inf__86ae4d25ae09
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_le_finset_inf__86ae4d25ae09
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:12.418803+00:00
-- url     : https://prove2.me/theorems/11a1dbdb-d99f-555d-bb5c-8f840d8566f0
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR le finset inf  86ae4d25ae09: P2 M Reciprocity Theory Chart Restriction G DVR le finset inf  86ae4d25ae09
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR le finset inf  86ae4d25ae09 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR le finset inf  86ae4d25ae09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L89-L90

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_le_finset_inf__86ae4d25ae09 {Y : Scheme.{0}} {κ : Type} {s : Finset κ} {F : κ → Y.Opens} {i : κ} (hi : i ∈ s) :
    s.inf F ≤ F i := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«le_finset_inf'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_le_finset_inf__86ae4d25ae09
