-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e
-- name    : P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:17.658609+00:00
-- url     : https://prove2.me/theorems/d4dd9ab3-b0e2-4b4e-a15e-d6c160940132
-- title:
--   P2 M Global Theory T length coker lsmul eq length ker add sum  275061a9a21e: P2 M Global Theory T length coker lsmul eq length ker add sum  275061a9a21e
-- statement:
--   The P2 M Global Theory T length coker lsmul eq length ker add sum  275061a9a21e construction uses the P2 M Global Theory T length coker lsmul eq length ker add sum  275061a9a21e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSumStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSumStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by sorry

alias «GlobalTheory».«T».«length_coker_lsmul_eq_length_ker_add_sum'» := P2M_GlobalTheory_T_length_coker_lsmul_eq_length_ker_add_sum__275061a9a21e
