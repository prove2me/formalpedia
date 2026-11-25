-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_zero__092417bce4c2
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_zero__092417bce4c2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:16.836092+00:00
-- url     : https://prove2.me/theorems/17194581-62e0-41b2-a138-ca44700e3330
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR rs zero  092417bce4c2: P2 M Reciprocity Theory Chart Restriction G DVR rs zero  092417bce4c2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR rs zero  092417bce4c2 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR rs zero  092417bce4c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L107-L107

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_zero__092417bce4c2 {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) : rs h (0 : Γ(Z, U)) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«rs_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_zero__092417bce4c2
