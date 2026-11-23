-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb
-- name    : P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:39.599499+00:00
-- url     : https://prove2.me/theorems/e9a9c20c-440b-4372-8a91-7a02a85417b6
-- title:
--   P2 M Global Theory cube Face Sequence   eq 2f890e00cceb: P2 M Global Theory cube Face Sequence   eq 2f890e00cceb
-- statement:
--   The P2 M Global Theory cube Face Sequence   eq 2f890e00cceb construction uses the P2 M Global Theory cube Face Sequence   eq 2f890e00cceb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L705-L711
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L705-L711

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
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he

theorem P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb (A : Cube.{v} ι R) (p : ℕ) :
    (cubeFaceSequence_shortExact he A).δ p (p + 1) rfl =
      homologyMap (cubeComplexMap (Cube.faceMap e i A)) p ≫
        (Int.negOnePow p • shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).inv := by sorry

alias «GlobalTheory».«cubeFaceSequence_δ_eq» := P2M_GlobalTheory_cubeFaceSequence___eq_2f890e00cceb
