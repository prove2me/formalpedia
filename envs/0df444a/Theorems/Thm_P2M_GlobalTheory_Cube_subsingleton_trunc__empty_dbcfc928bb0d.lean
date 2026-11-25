-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d
-- name    : P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:14.097554+00:00
-- url     : https://prove2.me/theorems/1a764443-21d2-4d19-aa48-07653c248461
-- title:
--   P2 M Global Theory Cube subsingleton trunc  empty dbcfc928bb0d: P2 M Global Theory Cube subsingleton trunc  empty dbcfc928bb0d
-- statement:
--   The P2 M Global Theory Cube subsingleton trunc  empty dbcfc928bb0d construction uses the P2 M Global Theory Cube subsingleton trunc  empty dbcfc928bb0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L779-L780
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L779-L780

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

theorem P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d (A : Cube.{v} ι R) : Subsingleton ((trunc₁ A).obj ∅) := by sorry

alias «GlobalTheory».«Cube».«subsingleton_trunc₁_empty» := P2M_GlobalTheory_Cube_subsingleton_trunc__empty_dbcfc928bb0d
