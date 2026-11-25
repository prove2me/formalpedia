-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817
-- name    : P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:00.895125+00:00
-- url     : https://prove2.me/theorems/d07ed945-bbca-4138-a7c0-4a7d0083328b
-- title:
--   P2 M Global Theory T exists ne zero algebra Map eq mul of formally Unramified  2991a8b24817: P2 M Global Theory T exists ne zero algebra Map eq mul of formally Unramified  2991a8b24817
-- statement:
--   The P2 M Global Theory T exists ne zero algebra Map eq mul of formally Unramified  2991a8b24817 construction uses the P2 M Global Theory T exists ne zero algebra Map eq mul of formally Unramified  2991a8b24817 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817 : ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 → ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by sorry

alias «GlobalTheory».«T».«exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified'» := P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817
