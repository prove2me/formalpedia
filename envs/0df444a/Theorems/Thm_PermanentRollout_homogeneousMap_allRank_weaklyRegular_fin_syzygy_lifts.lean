-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts
-- name    : PermanentRollout.homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/6b680592-72a7-41b0-880f-9698e3bceb63
-- title:
--   PermanentRollout.homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators

theorem PermanentRollout.homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts
    {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) :
    ∀ (n : ℕ) (f : Fin n → R),
      RingTheory.Sequence.IsWeaklyRegular S
        (List.ofFn fun i => q (f i)) →
      ∀ a : Fin n → S,
        (∑ i, a i * q (f i)) = 0 →
          ∃ b : Fin n → R,
            (∀ i, q (b i) = a i) ∧
              (∑ i, b i * f i) = 0 := by sorry
