-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P30_shannon_entropy_equality_iff_transpose_recovery
-- name    : QAlgorithms.Papers.Independent.Bridge50.P30.shannon_entropy_equality_iff_transpose_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:35:03.635451+00:00
-- url     : https://prove2.me/theorems/b2517255-f69a-4d16-a94c-4b0ae37e16ea
-- title:
--   Shannon entropy equality is equivalent to transpose recovery
-- statement:
--   Let $N\ge1$, let $p\in\mathbb R^N$ have nonnegative entries summing to one, and let $B$ be a real $N\times N$ matrix with nonnegative entries and all row and column sums equal to one. For a probability vector $r$, write $H(r)=-\sum_i r_i\log_2 r_i$, using $0\log_2 0=0$. Matrices act on column vectors and $B^T$ is the ordinary real transpose. Then
--
--   $$
--   H(Bp)=H(p)\quad\Longleftrightarrow\quad B^TBp=p.
--   $$
--
--   The characterization permits zero probabilities, zero matrix entries and permutation matrices. It describes exactly when a bi-stochastic average preserves Shannon entropy.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, PDF p. 6, Corollary 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.6, Corollary 3.2. The p.5 conventions allow zero probabilities and
zero matrix entries. The transpose is the ordinary real transpose, acting on columns. -/
theorem shannon_entropy_equality_iff_transpose_recovery
    {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ)
    (B : Matrix (Fin N) (Fin N) ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin N))
    (hB : B ∈ doublyStochastic ℝ (Fin N)) :
    classicalEntropy (B.mulVec p) = classicalEntropy p ↔
      B.transpose.mulVec (B.mulVec p) = p := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P30

end
