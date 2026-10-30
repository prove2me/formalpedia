-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_separable_product_minimum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.separable_product_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:40:46.138899+00:00
-- url     : https://prove2.me/theorems/556508f3-8a39-4779-a5c2-b14e55a3eb41
-- title:
--   Lemma 3: multiplicativity of minimal product overlap and kernel consequence
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P\in M_{d_1}\otimes M_{d_2}$ be separable positive, and let $\mu$ be its minimum expectation over unit product vectors. For every positive $n$,
--   $$\min_{\|\Psi\|=\|\Phi\|=1}\langle\Psi\otimes\Phi|P^{\otimes n}|\Psi\otimes\Phi\rangle=\mu^n.$$
--   Here $\Psi\in(\mathbb C^{d_1})^{\otimes n}$ and $\Phi\in(\mathbb C^{d_2})^{\otimes n}$ are arbitrary local vectors, including vectors entangled among the copies. Both minima are attained. If $\ker P$ has no nonzero product vector, then neither does $\ker P^{\otimes n}$. The zero matrix is permitted.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 5, Lemma 3: multiplicativity of minimal product overlap and kernel consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Lemma 3, PDF pp.5--6: minimum attainment, multiplicativity, and kernel consequence.
The local vectors range over ENTIRE local n-copy spaces; P=0 is allowed. -/
theorem separable_product_minimum [Nonempty A] [Nonempty B] (P : Mat (A × B))
    (hP : Entanglement.IsSeparablePositive P) :
    IsLeast (productValues P) (minProduct P) ∧
    ∀ n : ℕ, 0 < n →
      IsLeast (productValues (copies P n)) (minProduct P ^ n) ∧
      minProduct (copies P n) = minProduct P ^ n ∧
      (NoProductKernel P → NoProductKernel (copies P n)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
