-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_Cocycle_constFn_zero__d707fc2ffe6e
-- name    : P2M_GlobalTheory_KS_Cocycle_constFn_zero__d707fc2ffe6e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:53.411107+00:00
-- url     : https://prove2.me/theorems/a278043c-7498-5f37-b71d-c4e542f965ee
-- title:
--   P2 M Global Theory KS Cocycle const Fn zero  d707fc2ffe6e: P2 M Global Theory KS Cocycle const Fn zero  d707fc2ffe6e
-- statement:
--   The P2 M Global Theory KS Cocycle const Fn zero  d707fc2ffe6e construction uses the P2 M Global Theory KS Cocycle const Fn zero  d707fc2ffe6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnZero.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnZero.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Cocycle

theorem P2M_GlobalTheory_KS_Cocycle_constFn_zero__d707fc2ffe6e {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    constFn q O (0 : K) = 0 := by sorry

alias «GlobalTheory».«KS».«Cocycle».«constFn_zero'» := P2M_GlobalTheory_KS_Cocycle_constFn_zero__d707fc2ffe6e
