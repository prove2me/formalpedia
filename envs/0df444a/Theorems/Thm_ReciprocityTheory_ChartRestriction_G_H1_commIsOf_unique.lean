-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_commIsOf_unique
-- name    : ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:28.848941+00:00
-- url     : https://prove2.me/theorems/56daedcb-aa46-4b0b-9ae9-590e4588b69a
-- title:
--   H1: comm Is Of unique
-- statement:
--   The H1 construction uses the comm Is Of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L184-L195

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S}
    (θx θy : ThetaGrp A L k T) (c c' : Γ(T.left, ⊤)ˣ) (h : CommIsOf A L k θx θy c) (h' : CommIsOf A L k θx θy c') :
    c = c' := by sorry
