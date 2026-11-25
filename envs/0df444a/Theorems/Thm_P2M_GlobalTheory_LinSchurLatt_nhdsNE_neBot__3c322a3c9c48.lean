-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LinSchurLatt_nhdsNE_neBot__3c322a3c9c48
-- name    : P2M_GlobalTheory_LinSchurLatt_nhdsNE_neBot__3c322a3c9c48
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:33.269386+00:00
-- url     : https://prove2.me/theorems/a66af166-6832-40d6-af3f-b61521817361
-- title:
--   P2 M Global Theory Lin Schur Latt nhds NE ne Bot  3c322a3c9c48: P2 M Global Theory Lin Schur Latt nhds NE ne Bot  3c322a3c9c48
-- statement:
--   The P2 M Global Theory Lin Schur Latt nhds NE ne Bot  3c322a3c9c48 construction uses the P2 M Global Theory Lin Schur Latt nhds NE ne Bot  3c322a3c9c48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasis.lean#L80-L88

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

theorem P2M_GlobalTheory_LinSchurLatt_nhdsNE_neBot__3c322a3c9c48 : (𝓝[≠] (0 : k)).NeBot := by sorry

alias «GlobalTheory».«LinSchurLatt».«nhdsNE_neBot'» := P2M_GlobalTheory_LinSchurLatt_nhdsNE_neBot__3c322a3c9c48
