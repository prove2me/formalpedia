-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed
-- name    : P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:14.747924+00:00
-- url     : https://prove2.me/theorems/baa8fa02-d6f2-4b05-a240-87d97a155787
-- title:
--   P2 M Global Theory Count Id map pow  f545ffa1a6ed: P2 M Global Theory Count Id map pow  f545ffa1a6ed
-- statement:
--   The P2 M Global Theory Count Id map pow  f545ffa1a6ed construction uses the P2 M Global Theory Count Id map pow  f545ffa1a6ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L30-L34

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

theorem P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (i : ℕ) :
    (A ^ i).map φ = (A.map φ) ^ i := by sorry

alias «GlobalTheory».«CountId».«map_pow'» := P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed
