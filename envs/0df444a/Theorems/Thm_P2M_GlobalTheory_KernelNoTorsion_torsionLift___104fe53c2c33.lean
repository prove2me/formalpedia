-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
-- name    : P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:32.815808+00:00
-- url     : https://prove2.me/theorems/27cc9880-4e3b-4eab-beb8-11b2fbbd3710
-- title:
--   P2 M Global Theory Kernel No Torsion torsion Lift   104fe53c2c33: P2 M Global Theory Kernel No Torsion torsion Lift   104fe53c2c33
-- statement:
--   The P2 M Global Theory Kernel No Torsion torsion Lift   104fe53c2c33 construction uses the P2 M Global Theory Kernel No Torsion torsion Lift   104fe53c2c33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L48-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KernelNoTorsion

theorem P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33 {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x := by sorry

alias «GlobalTheory».«KernelNoTorsion».«torsionLift_ι» := P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
