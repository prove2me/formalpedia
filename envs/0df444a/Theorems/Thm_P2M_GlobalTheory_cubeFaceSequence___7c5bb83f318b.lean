-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b
-- name    : P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:19.249798+00:00
-- url     : https://prove2.me/theorems/96bd12ee-c4e4-4c89-92e0-9cc128e310b2
-- title:
--   P2 M Global Theory cube Face Sequence   7c5bb83f318b: P2 M Global Theory cube Face Sequence   7c5bb83f318b
-- statement:
--   The P2 M Global Theory cube Face Sequence   7c5bb83f318b construction uses the P2 M Global Theory cube Face Sequence   7c5bb83f318b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L594-L632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L594-L632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
variable (he : Set.range e = {i}ᶜ)

theorem P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b (A : Cube.{v} ι R) (p : ℕ) :
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl ≫
        (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
      (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p := by sorry

alias «GlobalTheory».«cubeFaceSequence_δ» := P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b
