-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_testingToApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.testingToApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:58:19.922975+00:00
-- url     : https://prove2.me/theorems/52c59e09-7f9e-4d26-bf6a-a070404d9eaa
-- title:
--   From testing to exponential approximation
-- statement:
--   Assume F1–F3 and fix $0<\varepsilon<1$. Compute the lower testing rate from the target and alternatives by
--   $$b_\varepsilon=\liminf_{n\to\infty}\frac{-\log_2\beta_{\varepsilon,n}}{n}.$$
--   For each $S>b_\varepsilon$, there are constants $K,\gamma>0$ and, at every sufficiently large positive length, CPTP $L_n$ and free $S_n$ satisfying $L_n\le_{\rm CP}2^{nS}S_n$ and $\|L_n-\mathcal N^{\otimes n}\|_\diamond\le Ke^{-\gamma n}$. This implication does not assume either ordinary limit in the Stein identity.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 14, Proposition 9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 9, computed lower testing limit without any assumed convergence, PDF pp.14–15. -/
theorem testingToApproximation [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ S : ℝ, (liminf (fun j : ℕ => exponent (power N (j+1)) (F (j+1)) eps / (j+1)) atTop) < S →
      ExponentialApproximation N F S := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
