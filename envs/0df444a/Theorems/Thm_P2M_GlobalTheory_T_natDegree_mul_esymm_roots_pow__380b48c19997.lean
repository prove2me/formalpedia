-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_natDegree_mul_esymm_roots_pow__380b48c19997
-- name    : P2M_GlobalTheory_T_natDegree_mul_esymm_roots_pow__380b48c19997
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:23.017016+00:00
-- url     : https://prove2.me/theorems/0c92104c-1b3a-4fbd-a35c-6180e9841b7e
-- title:
--   P2 M Global Theory T nat Degree mul esymm roots pow  380b48c19997: P2 M Global Theory T nat Degree mul esymm roots pow  380b48c19997
-- statement:
--   The P2 M Global Theory T nat Degree mul esymm roots pow  380b48c19997 construction uses the P2 M Global Theory T nat Degree mul esymm roots pow  380b48c19997 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeMulEsymmRootsPowStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeMulEsymmRootsPowStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_natDegree_mul_esymm_roots_pow__380b48c19997 : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by sorry

alias «GlobalTheory».«T».«natDegree_mul_esymm_roots_pow'» := P2M_GlobalTheory_T_natDegree_mul_esymm_roots_pow__380b48c19997
