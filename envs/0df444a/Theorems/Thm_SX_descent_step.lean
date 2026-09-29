-- Prove2me | Theorems.Thm_SX_descent_step
-- name    : SX.descent_step
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T11:12:13.685729+00:00
-- url     : https://prove2.me/theorems/d2ebac57-a209-470b-a366-8430f6fe9ff3
-- title:
--   The descent step of Schneider's method
-- statement:
--   **The descent step** — the analytic and arithmetic halves of Schneider's method, in one statement.
--
--   Under the standing hypotheses, if the auxiliary function has coefficients of size at most $e^{cLM}$ and vanishes at every lattice point $\sum_j m_j y_j$ with all $m_j < N$, for some $N \ge M$, then it vanishes at every such point with all $m_j < N+1$.
--
--   Iterating from the $M$ supplied by the Siegel step, the function vanishes on the whole lattice.
--
--   **Why the two halves cannot be separate rungs.** The analytic half says: an entire function with $N^l$ prescribed zeros is small on a disc, by dividing out the zeros and applying the maximum modulus principle. The arithmetic half says: the value at a new lattice point is an algebraic integer, so if it is non-zero its norm is at least 1. Each half is an inequality about a single value $F(w)$, and nothing links them except the balance of parameters, which is the body of the proof rather than a lemma. Stated apart they do not meet; stated together they are the induction step.
--
--   The balance is $N^l \log 2$ against $O(N^{l/d + 1})$, and it closes precisely when $dl > d + l$.
--
--   **Where it anchors.** `Complex.norm_le_of_forall_mem_frontier_norm_le` for the maximum modulus; `NumberField.one_le_house_of_isIntegral` and `NumberField.norm_norm_le_norm_mul_house_pow` for the arithmetic. The "many prescribed zeros implies small" estimate does **not** exist in Mathlib and has to be built — note that `Analysis/Complex/Schwarz.lean` is the ball-to-ball Schwarz lemma, which is a different statement. This is where essentially all the difficulty of the theorem lives.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley 1966, Ch. 2; K. Ramachandra, Contributions to the theory of transcendental numbers I, Acta Arith. 14 (1968) 65-72; M. Waldschmidt, Auxiliary functions in transcendence proofs, arXiv:0908.4024, sections 3.1.3 and 3.4 (Theorem 3.9); M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Springer 2000, Theorem 1.12.

import Definitions.Def_SX

open Complex

namespace SX

theorem descent_step
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K)
    (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : ℕ, 0 < L → (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l →
      ∀ p : (Fin d → ℕ) → ℤ, (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) →
        ∀ N : ℕ, M ≤ N →
          (∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0) →
          (∀ m : Fin l → ℕ, (∀ j, m j < N + 1) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  sorry

end SX
