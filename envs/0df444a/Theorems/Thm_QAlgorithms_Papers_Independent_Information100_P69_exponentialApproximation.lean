-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_exponentialApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.exponentialApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:53:47.671178+00:00
-- url     : https://prove2.me/theorems/be03df7d-bc55-4fa2-932e-ebabc13471d3
-- title:
--   Exponential free-channel approximation
-- statement:
--   Under the three basic family axioms of Theorem 2, fix any $S>R_{\mathcal F}(\mathcal N)$. There are $K_S,\gamma_S>0$ and a threshold, independent of blocklength, such that every sufficiently large positive integer $n$ admits channels $S_n\in\mathcal F_n$ and $L_n$ with
--   $$L_n\le_{\rm CP}2^{nS}S_n,\qquad\|L_n-\mathcal N^{\otimes n}\|_\diamond\le K_Se^{-\gamma_S n}.$$
--   These channels are chosen before every input, reference, and test. The constants may depend on the target, family, and rate margin. This gives exactly trace-preserving approximation with exponential accuracy.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 7, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Theorem 3 (exponential free-channel approximation), PDF p.7. -/
theorem exponentialApproximation [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) :
    ∀ S : ℝ, rate N F < S → ExponentialApproximation N F S := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
