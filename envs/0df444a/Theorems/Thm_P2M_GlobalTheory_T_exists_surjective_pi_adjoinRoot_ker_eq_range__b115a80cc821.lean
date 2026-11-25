-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821
-- name    : P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:48.735+00:00
-- url     : https://prove2.me/theorems/2582eb4c-2007-41d6-ad6e-9136b23c2328
-- title:
--   P2 M Global Theory T exists surjective pi adjoin Root ker eq range  b115a80cc821: P2 M Global Theory T exists surjective pi adjoin Root ker eq range  b115a80cc821
-- statement:
--   The P2 M Global Theory T exists surjective pi adjoin Root ker eq range  b115a80cc821 construction uses the P2 M Global Theory T exists surjective pi adjoin Root ker eq range  b115a80cc821 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRangeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjectivePiAdjoinRootKerEqRangeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821 : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) [Fact (Irreducible f)], ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧ (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧ LinearMap.ker π = LinearMap.range (aeval g f) ∧ Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by sorry

alias «GlobalTheory».«T».«exists_surjective_pi_adjoinRoot_ker_eq_range'» := P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821
