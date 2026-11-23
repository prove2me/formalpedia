-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1
-- name    : P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:57.433446+00:00
-- url     : https://prove2.me/theorems/72b5d016-14cb-4c7c-a889-aba5b14c631b
-- title:
--   P2 M Global Theory Count Id map vec Mul  4969f4544bd1: P2 M Global Theory Count Id map vec Mul  4969f4544bd1
-- statement:
--   The P2 M Global Theory Count Id map vec Mul  4969f4544bd1 construction uses the P2 M Global Theory Count Id map vec Mul  4969f4544bd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']

theorem P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1 (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (fun i => φ ((v ᵥ* A) i)) = (fun i => φ (v i)) ᵥ* A.map φ := by sorry

alias «GlobalTheory».«CountId».«map_vecMul'» := P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1
