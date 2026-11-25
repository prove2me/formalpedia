-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CuspGL_exists_conj_of_aeval__equiv_6dd8055a4950
-- name    : P2M_GlobalTheory_CuspGL_exists_conj_of_aeval__equiv_6dd8055a4950
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:03.194803+00:00
-- url     : https://prove2.me/theorems/8bf0c35d-a4d3-4d61-9d1b-b20dc97311da
-- title:
--   P2 M Global Theory Cusp GL exists conj of aeval  equiv 6dd8055a4950: P2 M Global Theory Cusp GL exists conj of aeval  equiv 6dd8055a4950
-- statement:
--   The P2 M Global Theory Cusp GL exists conj of aeval  equiv 6dd8055a4950 construction uses the P2 M Global Theory Cusp GL exists conj of aeval  equiv 6dd8055a4950 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ConjOfPrimaryFinrankKerPowEq.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ConjOfPrimaryFinrankKerPowEq.lean#L9-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem P2M_GlobalTheory_CuspGL_exists_conj_of_aeval__equiv_6dd8055a4950 {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g g' : Module.End F V) (φ : Module.AEval' g ≃ₗ[F[X]] Module.AEval' g') :
    ∃ e : V ≃ₗ[F] V, e.conj g = g' := by sorry

alias «GlobalTheory».«CuspGL».«exists_conj_of_aeval'_equiv» := P2M_GlobalTheory_CuspGL_exists_conj_of_aeval__equiv_6dd8055a4950
