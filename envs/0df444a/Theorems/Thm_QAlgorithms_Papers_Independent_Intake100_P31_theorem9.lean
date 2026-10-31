-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P31_theorem9
-- name    : QAlgorithms.Papers.Independent.Intake100.P31.theorem9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:02:26.239324+00:00
-- url     : https://prove2.me/theorems/d8baceee-c9c9-4fa4-9850-79038b142538
-- title:
--   Theorem 9: ordinary 2-almost universality does not suffice for strong secrecy
-- statement:
--   For every block length $n\ge1$ and dimension $0\le t<n$, there exists a finite nonempty uniform family of dimension-$t$ binary codes $C_r\le\mathbb F_2^n$, with ordinary universality parameter two, selected before the noise parameter. Alice's message is a uniform quotient coset, transmitted by selecting a uniform word within it. Bob receives the word noiselessly and Eve receives that word through an independent BSC of parameter $p$. For the actual classical quotient-message/Eve mutual information $I_r$,
--
--   $$\forall p\in[0,1]\setminus\{1/2\},\qquad\mathbb E_r I_r\ge1-h(p)>0.$$
--
--   Consequently these families have a leakage floor that persists with block length. The classical broadcast channel is distinct from a quantum complementary channel. The excluded zero-capacity case and the non-strict lower bound correct the printed statement and proof.
-- source:
--   Dual universality of hash functions and its applications to quantum cryptography, arXiv:1101.0064v4, PDF p. 15, Theorem 9: ordinary 2-almost universality does not suffice for strong secrecy

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P31

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms

local instance {n : ℕ} (C : BinaryLinearCode n) : Fintype C := Fintype.ofFinite C

/-- PDF p.15, Theorem 9: appended-zero subcodes give a constant leakage floor
at every block length, for each feasible dimension t<n. The family is chosen
before p. Correct the missing nonzero-capacity condition p≠1/2 and the proof's
strict inequality to ≥1-h(p). This is a classical broadcast channel, not the
complementary channel of a noiseless quantum channel. -/
theorem theorem9 {n t : ℕ} (hn : 0 < n) (ht : t < n) :
    ∃ (N : ℕ) (hN : 0 < N) (C : Fin N → BinaryLinearCode n),
      (∀ r, Module.finrank (ZMod 2) (C r) = t) ∧ UniversalAt C t 2 ∧
      ∀ p : ℝ, p ∈ Set.Icc 0 1 → p ≠ 1 / 2 →
        avg (fun r => classicalLeak (C r) p) ≥ 1 - binEntropy2 p ∧
        0 < 1 - binEntropy2 p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P31

end
