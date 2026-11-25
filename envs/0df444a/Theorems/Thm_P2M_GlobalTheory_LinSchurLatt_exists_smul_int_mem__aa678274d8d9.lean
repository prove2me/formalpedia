-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LinSchurLatt_exists_smul_int_mem__aa678274d8d9
-- name    : P2M_GlobalTheory_LinSchurLatt_exists_smul_int_mem__aa678274d8d9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:45.054781+00:00
-- url     : https://prove2.me/theorems/5aa61ce6-7e15-429b-b502-c5be15b72d3e
-- title:
--   P2 M Global Theory Lin Schur Latt exists smul int mem  aa678274d8d9: P2 M Global Theory Lin Schur Latt exists smul int mem  aa678274d8d9
-- statement:
--   The P2 M Global Theory Lin Schur Latt exists smul int mem  aa678274d8d9 construction uses the P2 M Global Theory Lin Schur Latt exists smul int mem  aa678274d8d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L99-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.LinSchurLatt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem P2M_GlobalTheory_LinSchurLatt_exists_smul_int_mem__aa678274d8d9 (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by sorry

alias «GlobalTheory».«LinSchurLatt».«exists_smul_int_mem'» := P2M_GlobalTheory_LinSchurLatt_exists_smul_int_mem__aa678274d8d9
