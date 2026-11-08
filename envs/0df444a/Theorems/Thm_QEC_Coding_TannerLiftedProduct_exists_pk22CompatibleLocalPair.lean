-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22CompatibleLocalPair
-- name    : QEC.Coding.TannerLiftedProduct.exists_pk22CompatibleLocalPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:10:23.805419+00:00
-- url     : https://prove2.me/theorems/41bbda3c-7a36-4db6-b2de-82588d74aaa6
-- title:
--   Tanner Lifted Product: exists pk22 Compatible Local Pair
-- statement:
--   Concrete simultaneous local-code selection at a source-compatible prime
--   degree.  No matrix property is supplied as an assumption: both matrices and
--   all their distance/product-expansion properties are obtained from the finite
--   six-event union bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatibleLocalPair.lean#L37-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatibleLocalPair.lean#L37-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {F : Type}
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LocalPairDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

theorem QEC.Coding.TannerLiftedProduct.exists_pk22CompatibleLocalPair
    (F : Type) [Field F] [Fintype F]
    (rate : ℝ) (hRate : rate < 1) :
    ∃ (t : Nat)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      pk22ScaleThreshold (Nat.card F) t ≤ Nat.nthRoot 6 a.blocks ∧
      pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
        Fintype.card (PK22Direction (Nat.card F) t a) ∧
      h.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      h'.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h).carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h').carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      2 * ((Fintype.card (PK22Check (Nat.card F) t a) : ℝ) +
          Fintype.card (PK22Check (Nat.card F) t a)) *
          Fintype.card (PK22Direction (Nat.card F) t a) ≤
        (1 - rate) *
          ((Fintype.card (PK22Direction (Nat.card F) t a) : ℝ) ^ 2 +
            4 * Fintype.card (PK22Check (Nat.card F) t a) *
              Fintype.card (PK22Check (Nat.card F) t a)) ∧
      2 * Real.sqrt (a.p : ℝ) ≤
        ((pk22SpectralCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 3 : Nat) : ℝ) := by sorry
