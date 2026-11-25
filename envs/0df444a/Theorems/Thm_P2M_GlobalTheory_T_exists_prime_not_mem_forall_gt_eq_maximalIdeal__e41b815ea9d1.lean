-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_prime_not_mem_forall_gt_eq_maximalIdeal__e41b815ea9d1
-- name    : P2M_GlobalTheory_T_exists_prime_not_mem_forall_gt_eq_maximalIdeal__e41b815ea9d1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:32.291497+00:00
-- url     : https://prove2.me/theorems/402ac33e-2540-4571-a8a1-d9fbe61c6d97
-- title:
--   P2 M Global Theory T exists prime not mem forall gt eq maximal Ideal  e41b815ea9d1: P2 M Global Theory T exists prime not mem forall gt eq maximal Ideal  e41b815ea9d1
-- statement:
--   The P2 M Global Theory T exists prime not mem forall gt eq maximal Ideal  e41b815ea9d1 construction uses the P2 M Global Theory T exists prime not mem forall gt eq maximal Ideal  e41b815ea9d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNotMemForallGtEqMaximalIdealStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNotMemForallGtEqMaximalIdealStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdealStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_prime_not_mem_forall_gt_eq_maximalIdeal__e41b815ea9d1 : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by sorry

alias «GlobalTheory».«T».«exists_prime_not_mem_forall_gt_eq_maximalIdeal'» := P2M_GlobalTheory_T_exists_prime_not_mem_forall_gt_eq_maximalIdeal__e41b815ea9d1
