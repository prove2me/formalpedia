-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen
-- name    : ReciprocityTheory.ChartRestriction.G.H1.val_constGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:30.951567+00:00
-- url     : https://prove2.me/theorems/cd7897d8-6260-48b6-8476-14dfbbe471a9
-- title:
--   H1: val const Gen
-- statement:
--   The H1 construction uses the val const Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/ThetaMove.lean#L94-L98

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

theorem ReciprocityTheory.ChartRestriction.G.H1.val_constGen {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (constGen A L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := by sorry
