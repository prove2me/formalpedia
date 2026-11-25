-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29
-- name    : P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:09.995043+00:00
-- url     : https://prove2.me/theorems/6b81498b-4b79-466c-9374-fc0699db45b7
-- title:
--   P2 M Global Theory Pairing Bound ord mul  d392fa035f29: P2 M Global Theory Pairing Bound ord mul  d392fa035f29
-- statement:
--   The P2 M Global Theory Pairing Bound ord mul  d392fa035f29 construction uses the P2 M Global Theory Pairing Bound ord mul  d392fa035f29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodDenominatorBound.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodDenominatorBound.lean#L12-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29 {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : ord_vw O (a * b) = ord_vw O a + ord_vw O b := by sorry

alias «GlobalTheory».«PairingBound».«ord_mul'» := P2M_GlobalTheory_PairingBound_ord_mul__d392fa035f29
