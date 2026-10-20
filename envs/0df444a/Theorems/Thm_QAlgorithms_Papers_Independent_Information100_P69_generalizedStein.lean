-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_generalizedStein
-- name    : QAlgorithms.Papers.Independent.Information100.P69.generalizedStein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:52:55.485852+00:00
-- url     : https://prove2.me/theorems/0ca8126b-5f52-40bd-826d-39dc919ab26b
-- title:
--   Generalized Stein identity for quantum channels
-- statement:
--   Let $\mathcal N:A\to B$ be a channel on nonzero finite-dimensional spaces. Let $\mathcal F_n$ be nonempty compact convex sets of channels, tensor closed across positive blocklengths, containing the tensor powers of a fixed faithful replacer with output $\omega$. Write $E_n=\inf_{M\in\mathcal F_n}D_{\rm ch}(\mathcal N^{\otimes n}\|M)$ and let $\beta_{\varepsilon,n}$ be the minimum worst-case alternative acceptance of a single reference-assisted parallel tester accepting the target with probability at least $1-\varepsilon$. There is a finite rate $R$, independent of $\varepsilon\in(0,1)$, such that
--   $$\lim_{n\to\infty}-\frac{1}{n}\log_2\beta_{\varepsilon,n}=R=\lim_{n\to\infty}\frac{E_n}{n},\qquad 0\le R\le\log_2\dim B-\log_2\lambda_{\min}(\omega).$$
--   Both limits run through all positive integers. This identifies the operational and regularized entropy rates.
--
--   Here $D_{\rm ch}$ is Umegaki relative entropy in bits maximized over a common normalized reference-assisted input; it retains $+\infty$ on support mismatch.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 7, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Theorem 2 (generalized Stein identity), arXiv:2609.30762v1, PDF p.7.
Both limits are ordinary limits over every positive integer. -/
theorem generalizedStein [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) :
    0 ≤ rate N F ∧ rate N F ≤ capacity omega ∧
    Tendsto (fun j : ℕ => resourceEntropy (power N (j+1)) (F (j+1)) / (j+1))
      atTop (nhds (ENNReal.ofReal (rate N F))) ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 →
      Tendsto (fun j : ℕ => exponent (power N (j+1)) (F (j+1)) eps / (j+1))
        atTop (nhds (rate N F)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
