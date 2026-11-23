-- Prove2me | Theorems.Thm_P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004
-- name    : P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:56.253634+00:00
-- url     : https://prove2.me/theorems/d7b85ce5-b376-4b17-ab15-63af190d3c78
-- title:
--   P2 M Global Theory mono cube Face Sequence   iff 45ee17f4c004: P2 M Global Theory mono cube Face Sequence   iff 45ee17f4c004
-- statement:
--   The P2 M Global Theory mono cube Face Sequence   iff 45ee17f4c004 construction uses the P2 M Global Theory mono cube Face Sequence   iff 45ee17f4c004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L713-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L713-L717

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

theorem P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004 (A : Cube.{v} ι R) (p : ℕ) :
    Mono ((cubeFaceSequence_shortExact he A).δ p (p + 1) rfl) ↔
      Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by sorry

alias «GlobalTheory».«mono_cubeFaceSequence_δ_iff» := P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004
