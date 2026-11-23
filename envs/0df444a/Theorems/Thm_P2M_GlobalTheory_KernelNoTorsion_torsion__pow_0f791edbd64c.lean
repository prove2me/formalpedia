-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
-- name    : P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:30.370797+00:00
-- url     : https://prove2.me/theorems/8767d5e6-b620-4238-8deb-c4b3670be5de
-- title:
--   P2 M Global Theory Kernel No Torsion torsion  pow 0f791edbd64c: P2 M Global Theory Kernel No Torsion torsion  pow 0f791edbd64c
-- statement:
--   The P2 M Global Theory Kernel No Torsion torsion  pow 0f791edbd64c construction uses the P2 M Global Theory Kernel No Torsion torsion  pow 0f791edbd64c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L56-L61

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

theorem P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by sorry

alias «GlobalTheory».«KernelNoTorsion».«torsionι_pow» := P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
