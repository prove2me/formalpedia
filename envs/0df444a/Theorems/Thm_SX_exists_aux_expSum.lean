-- Prove2me | Theorems.Thm_SX_exists_aux_expSum
-- name    : SX.exists_aux_expSum
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T11:11:52.943776+00:00
-- url     : https://prove2.me/theorems/f0a028dd-7409-4134-b87b-24b2921be5ae
-- title:
--   Existence of the auxiliary exponential polynomial (Siegel step)
-- statement:
--   **The auxiliary function exists** — the Siegel step of Schneider's method.
--
--   Suppose every $e^{x_i y_j}$ lies in a number field $K$, with $d + l < dl$ and the two families $\mathbb{Q}$-linearly independent. Then there is a constant $c > 0$ such that for all large $M$ there is a degree bound $L$ with $L^d \le c\,M^l$, and integer coefficients $p_\lambda$, not all zero, of size $|p_\lambda| \le e^{cLM}$, for which the exponential polynomial
--   $$F(z) \;=\; \sum_{\lambda} p_\lambda\, e^{\langle \lambda, x\rangle z}$$
--   vanishes at every lattice point $\sum_j m_j y_j$ with all $m_j < M$.
--
--   The count is the whole point: $M^l$ linear conditions against $L^d$ unknowns, and $d + l < dl$ is exactly what makes the system underdetermined enough for Siegel's lemma to return a small non-zero solution.
--
--   **Where it anchors.** `NumberField.house.exists_ne_zero_int_vec_house_le` — Siegel's lemma over a number field — together with the house API (`house_mul_le`, `house_pow_le`, `house_sum_le_sum_house`). The coefficient matrix has entries $\prod_i \prod_j (e^{x_i y_j})^{\lambda_i m_j}$, which is why the bundle's `exp_expExponent_mul_latticeSum` is needed to see the entries as algebraic integers at all.
--
--   **Note that $c$ is quantified before $M$.** That ordering is deliberate and load-bearing: the descent step consumes the same $c$ uniformly, and a constant fixed after $M$ would not compose.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley 1966, Ch. 2; K. Ramachandra, Contributions to the theory of transcendental numbers I, Acta Arith. 14 (1968) 65-72; M. Waldschmidt, Auxiliary functions in transcendence proofs, arXiv:0908.4024, sections 3.1.3 and 3.4 (Theorem 3.9); M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Springer 2000, Theorem 1.12.

import Definitions.Def_SX

open Complex

namespace SX

theorem exists_aux_expSum
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l ∧
        ∃ p : (Fin d → ℕ) → ℤ,
          (∃ lam ∈ SX.box d L, p lam ≠ 0) ∧
          (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) ∧
          (∀ m : Fin l → ℕ, (∀ j, m j < M) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  sorry

end SX
