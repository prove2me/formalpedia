-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fst_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.fst_restrict
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:04.743473+00:00
-- url     : https://prove2.me/theorems/58d93e49-ef8e-5a35-a3b4-9890983e748d
-- title:
--   Chart: fst restrict
-- statement:
--   The Chart construction uses the fst restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L37-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.fst_restrict (s : S) (A : Type) [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
    [IsScalarTower S (Localization.Away s) A] :
    (TrivSqZeroExt.fstHom (Localization.Away s) A A).restrictScalars S = TrivSqZeroExt.fstHom S A A := by sorry
