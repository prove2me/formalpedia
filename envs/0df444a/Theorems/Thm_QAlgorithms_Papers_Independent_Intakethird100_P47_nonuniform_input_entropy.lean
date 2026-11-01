-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_nonuniform_input_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.nonuniform_input_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:38:00.234296+00:00
-- url     : https://prove2.me/theorems/53a0a59f-d65b-4180-ae28-4ccfb89c1631
-- title:
--   Nonuniform private inputs have lower entropy cost
-- statement:
--   Let $A$ and $B$ be independent private binary settings, each with probability $r\in[0,1]$ of input zero. Let $h_2(r)=-r\log_2r-(1-r)\log_2(1-r)$, with $0\log 0=0$, and let $H(A,B)$ be Shannon entropy in bits. Then
--   $$
--   H(A,B)=2h_2(r),\qquad r\ne\tfrac12\ \Longrightarrow\ H(A,B)<2.
--   $$
--   In particular $r_*=(\sqrt5-1)/2$ lies strictly between zero and one and has $H(A,B)<2$. This is the asymptotic Shannon randomness cost of the independent input source, not a finite-seed length or a security statement for correlated adversarial randomness.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 6, IV B / VII A: nonuniform inputs require less randomness

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- IV B / VII A, PDF pp.6,8–9: nonuniform independent private settings cost less
Shannon entropy than two fair bits; the ideal chosen bias is included explicitly.
This is a population entropy statement, not an exact finite random-seed length. -/
theorem nonuniform_input_entropy :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      pairEntropy (binarySettingLaw r r) = 2 * binEntropy2 r ∧
      (r ≠ 1 / 2 → pairEntropy (binarySettingLaw r r) < 2)) ∧
    (0 < (Real.sqrt 5 - 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < 1) ∧
    pairEntropy (binarySettingLaw ((Real.sqrt 5 - 1) / 2) ((Real.sqrt 5 - 1) / 2)) < 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
