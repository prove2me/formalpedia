-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45
-- name    : P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:58.243615+00:00
-- url     : https://prove2.me/theorems/9cd6d4bf-c7eb-5365-bc21-c472ca56d046
-- title:
--   P2 M Global Theory Cube trunc Incl bijective 15000a487b45: P2 M Global Theory Cube trunc Incl bijective 15000a487b45
-- statement:
--   The P2 M Global Theory Cube trunc Incl bijective 15000a487b45 construction uses the P2 M Global Theory Cube trunc Incl bijective 15000a487b45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L782-L788
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L782-L788

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

theorem P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45 (A : Cube.{v} (ι ⊕ₗ κ) R) {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    Function.Bijective ((trunc₂Incl A).app (sumVertex s t)).hom := by sorry

alias «GlobalTheory».«Cube».«trunc₂Incl_bijective» := P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45
