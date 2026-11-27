-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord__1fcb71323d4a
-- name    : P2M_GlobalTheory_T_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord__1fcb71323d4a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:18.919564+00:00
-- url     : https://prove2.me/theorems/0e6e18b0-5440-5d8c-b97a-34411a3cea97
-- title:
--   P2 M Global Theory T finsum ord mul inertia Deg eq finrank mul ord  1fcb71323d4a: P2 M Global Theory T finsum ord mul inertia Deg eq finrank mul ord  1fcb71323d4a
-- statement:
--   The P2 M Global Theory T finsum ord mul inertia Deg eq finrank mul ord  1fcb71323d4a construction uses the P2 M Global Theory T finsum ord mul inertia Deg eq finrank mul ord  1fcb71323d4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrdMulInertiaDegEqFinrankMulOrdStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrdMulInertiaDegEqFinrankMulOrdStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord__1fcb71323d4a : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by sorry

alias «GlobalTheory».«T».«finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord'» := P2M_GlobalTheory_T_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord__1fcb71323d4a
