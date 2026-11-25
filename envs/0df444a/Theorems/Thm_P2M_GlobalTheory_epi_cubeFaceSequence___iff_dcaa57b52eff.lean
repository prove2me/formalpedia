-- Prove2me | Theorems.Thm_P2M_GlobalTheory_epi_cubeFaceSequence___iff_dcaa57b52eff
-- name    : P2M_GlobalTheory_epi_cubeFaceSequence___iff_dcaa57b52eff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:59.963401+00:00
-- url     : https://prove2.me/theorems/f5412003-96e5-4118-828a-4008f642f8cb
-- title:
--   P2 M Global Theory epi cube Face Sequence   iff dcaa57b52eff: P2 M Global Theory epi cube Face Sequence   iff dcaa57b52eff
-- statement:
--   The P2 M Global Theory epi cube Face Sequence   iff dcaa57b52eff construction uses the P2 M Global Theory epi cube Face Sequence   iff dcaa57b52eff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L719-L722
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L719-L722

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

theorem P2M_GlobalTheory_epi_cubeFaceSequence___iff_dcaa57b52eff (A : Cube.{v} ι R) (p : ℕ) :
    Epi ((cubeFaceSequence_shortExact he A).δ p (p + 1) rfl) ↔
      Epi (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) := by sorry

alias «GlobalTheory».«epi_cubeFaceSequence_δ_iff» := P2M_GlobalTheory_epi_cubeFaceSequence___iff_dcaa57b52eff
