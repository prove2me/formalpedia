-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090
-- name    : P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:20.501666+00:00
-- url     : https://prove2.me/theorems/2fd7804d-eeb4-4fcb-b6a8-ac55c29e5486
-- title:
--   P2 M Global Theory Frame Value val At  sec 9a5221679090: P2 M Global Theory Frame Value val At  sec 9a5221679090
-- statement:
--   The P2 M Global Theory Frame Value val At  sec 9a5221679090 construction uses the P2 M Global Theory Frame Value val At  sec 9a5221679090 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean#L99-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}

theorem P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090 (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    valAt' y (L.wchart φ j) (s.f j) = secVal u hL s y z * frameProd u ε z j := by sorry

alias «GlobalTheory».«FrameValue».«valAt'_sec» := P2M_GlobalTheory_FrameValue_valAt__sec_9a5221679090
