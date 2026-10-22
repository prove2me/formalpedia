-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_squeezing_majorization_chain
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.squeezing_majorization_chain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:18:31.898087+00:00
-- url     : https://prove2.me/theorems/28f74d3b-daae-4eac-aea0-0a33fb65ffcd
-- title:
--   Fixed Fock input majorization under increasing squeezing, Eq.(15)
-- statement:
--   For a nonnegative integer $k$ and $0\le\lambda'<\lambda<1$, write $p_n^{(k)}(x)=(1-x^2)^{k+1}x^{2n}\binom{n+k}{n}$ for the squared Schmidt law of the physical amplifier dilation with number-state input $|k\rangle$. Then
--
--   $$
--   p^{(k)}(\lambda')\succ p^{(k)}(\lambda).
--   $$
--
--   Both laws are normalized, and the order is defined by their decreasing partial sums. The endpoint $\lambda'=0$ is included.
--
--   This orders the physical outputs at fixed Fock input as squeezing increases. The exact countable protocol of Appendix 5d supports the conclusion independently of the inconsistent printed beta-function transition matrix.
--
--   There also exists a real kernel $R_{nm}$ with nonnegative entries, convergent column sums one and summable row sums at most one, such that $R_{nm}=0$ for $n<m$ and $p_n^{(k)}(\lambda)=\sum_m R_{nm}p_m^{(k)}(\lambda')$, with convergence for every row. This is the triangular witness claimed in (A.28)–(A.33), independently of the deferred printed beta-function entry formula.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 9, (15), Appendix 4d and 5d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.3-4,7-10, (15) and Appendix 5d.
Increasing squeezing decreases the squared-Schmidt majorization order.
A lower-triangular column-stochastic, row-subunital witness exists, as claimed
in A.28-A.33; its defective printed beta entry formula is not imposed.
The unsqueezed endpoint is included directly, without negative powers. -/
theorem squeezing_majorization_chain (k : ℕ) (lambda target : ℝ)
    (ht : 0 ≤ target) (hlt : target < lambda) (hlu : lambda < 1) :
    ProbabilityMajorizes (fockSchmidtWeight k target) (fockSchmidtWeight k lambda) ∧
    ∃ R : ℕ → ℕ → ℝ, CountableSubunitalStochastic R ∧
      (∀ n m : ℕ, n < m → R n m = 0) ∧
      ∀ n : ℕ, HasSum (fun m => R n m * fockSchmidtWeight k target m)
        (fockSchmidtWeight k lambda n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
