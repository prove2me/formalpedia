-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_N_embX_inv_mul_mem_KOne__092498a488ab
-- name    : P2M_GlobalTheory_T_exists_N_embX_inv_mul_mem_KOne__092498a488ab
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:56.596881+00:00
-- url     : https://prove2.me/theorems/7a1c01c6-b329-545f-9821-38fef973705f
-- title:
--   P2 M Global Theory T exists N emb X inv mul mem KOne  092498a488ab: P2 M Global Theory T exists N emb X inv mul mem KOne  092498a488ab
-- statement:
--   The P2 M Global Theory T exists N emb X inv mul mem KOne  092498a488ab construction uses the P2 M Global Theory T exists N emb X inv mul mem KOne  092498a488ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsNEmbXInvMulMemKOneStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsNEmbXInvMulMemKOneStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNEmbXInvMulMemKOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNEmbXInvMulMemKOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_N_embX_inv_mul_mem_KOne__092498a488ab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k), n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧ (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by sorry

alias «GlobalTheory».«T».«exists_N_embX_inv_mul_mem_KOne'» := P2M_GlobalTheory_T_exists_N_embX_inv_mul_mem_KOne__092498a488ab
