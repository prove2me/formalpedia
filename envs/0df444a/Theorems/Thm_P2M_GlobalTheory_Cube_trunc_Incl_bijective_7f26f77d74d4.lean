-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4
-- name    : P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:20.527986+00:00
-- url     : https://prove2.me/theorems/76d7293a-9276-458d-b39f-03ca90d6cb37
-- title:
--   P2 M Global Theory Cube trunc Incl bijective 7f26f77d74d4: P2 M Global Theory Cube trunc Incl bijective 7f26f77d74d4
-- statement:
--   The P2 M Global Theory Cube trunc Incl bijective 7f26f77d74d4 construction uses the P2 M Global Theory Cube trunc Incl bijective 7f26f77d74d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L774-L777
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L774-L777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
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
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]

theorem P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4 (A : Cube.{v} ι R) {s : Finset ι} (hs : s.Nonempty) :
    Function.Bijective ((trunc₁Incl A).app s).hom := by sorry

alias «GlobalTheory».«Cube».«trunc₁Incl_bijective» := P2M_GlobalTheory_Cube_trunc_Incl_bijective_7f26f77d74d4
