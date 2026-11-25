-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069
-- name    : P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:32.022458+00:00
-- url     : https://prove2.me/theorems/5d44ec90-8966-4750-b055-9f4467f0d6db
-- title:
--   P2 M Global Theory Unit Cocycle lmul  eq one 7cd501a29069: P2 M Global Theory Unit Cocycle lmul  eq one 7cd501a29069
-- statement:
--   The P2 M Global Theory Unit Cocycle lmul  eq one 7cd501a29069 construction uses the P2 M Global Theory Unit Cocycle lmul  eq one 7cd501a29069 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L36-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069 {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : Algebra.TensorProduct.lmul' R c = (1 : B) := by sorry

alias «GlobalTheory».«UnitCocycle».«lmul'_eq_one» := P2M_GlobalTheory_UnitCocycle_lmul__eq_one_7cd501a29069
