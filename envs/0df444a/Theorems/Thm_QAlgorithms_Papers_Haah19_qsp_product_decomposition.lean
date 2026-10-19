-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Haah19_qsp_product_decomposition
-- name    : QAlgorithms.Papers.Haah19.qsp_product_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:03:54.622342+00:00
-- url     : https://prove2.me/theorems/95c9db17-3320-46ee-9516-59aaa86dd50c
-- title:
--   Haah Theorem 2: SU(2)-valued Laurent polynomials of fixed parity factor uniquely into primitive matrices
-- statement:
--   This is the product-decomposition theorem underlying quantum signal processing.
--
--   For an integer $n\ge 0$ let $\mathcal P_n$ be the set of Laurent polynomials $F(t)=\sum_{j=-n}^{n}C_j t^j$ with coefficients $C_j\in\mathrm{Mat}(2;\mathbb C)$ such that $F(\eta)\in SU(2)$ for every $\eta\in\mathbb C$ with $|\eta|=1$. Such an $F$ has degree $n$ if $C_n\ne 0$ or $C_{-n}\ne 0$. Let $\mathcal E_n\subseteq\mathcal P_n$ consist of those $F$ whose exponents lie in $\{-n,-n+2,\dots,n-2,n\}$, i.e. $C_{-n+k}=0$ for every odd $k$. For a rank-one orthogonal projector $P$ on $\mathbb C^2$ the primitive matrix is
--
--   $$E_P(t)=tP+t^{-1}(I-P).$$
--
--   Then:
--
--   1. For every $n$ and all rank-one projectors $P_1,\dots,P_n$, the product $E_{P_1}(t)\cdots E_{P_n}(t)$ belongs to $\mathcal E_n$.
--   2. Every $F\in\mathcal E_n$ of degree $n$ admits exactly one tuple $(E_0,P_1,\dots,P_n)$, with $E_0\in SU(2)$ independent of $t$ and each $P_j$ a rank-one projector, such that
--   $$F(t)=E_0\,E_{P_1}(t)E_{P_2}(t)\cdots E_{P_n}(t)$$
--   as Laurent polynomials.
--   3. If $n\ge 1$ and $F(t)=C_{-n}t^{-n}+\dots+C_nt^n$ is decomposed as in 2, then the last projector is
--   $$P_n=\frac{C_n^{\dagger}C_n}{\operatorname{Tr}(C_n^{\dagger}C_n)}.$$
--
--   The theorem characterizes exactly which polynomial functions $U(1)\to SU(2)$ are achievable by alternating controlled-$W$ and controlled-$W^\dagger$ with single-qubit rotations, and item 3 gives the peeling step of the classical algorithm that computes the rotation sequence.
--
--   **Formalization Note** The source's $E_0$ is "a unitary"; because $\det E_P(\eta)=1$ and $F(\eta)\in SU(2)$ on the unit circle, any unitary $E_0$ in such a decomposition has determinant 1, so ranging over $SU(2)$ is equivalent. Uniqueness is of the whole ordered tuple. The projector $P_n$ is the factor at index $n-1$ of a $0$-indexed family. That $C_n\ne 0$ (so the trace is nonzero) is a fact the source proves, not a hypothesis.
-- source:
--   Product Decomposition of Periodic Functions in Quantum Signal Processing (Haah), arXiv:1806.10236v4, Theorem 2, PDF p. 4. https://arxiv.org/abs/1806.10236v4 . PDF SHA-256: 7e084543c526c18c27aa5295e46db182ace233cff0d1cdf49e72256c3bfa436d.

import Definitions.Def_QAlgorithms_Defs_LaurentQSP
set_option autoImplicit false

namespace QAlgorithms.Papers.Haah19

open QAlgorithms
open scoped Matrix

/-- Haah Theorem 2 (p.4; proof pp.4–5). Write `E_P(t) = tP + t^{−1}(I − P)` for a rank-1
orthogonal projector `P` (Eq. (2), p.3).

1. For every `n` and rank-1 projectors `P_1, …, P_n`, the product `E_{P_1}(t) ⋯ E_{P_n}(t)`
   belongs to `E_n`.
2. Every `F(t) ∈ E_n` of degree `n` has a unique decomposition `F(t) = E_0 E_{P_1}(t) ⋯ E_{P_n}(t)`
   (Eq. (3)) with `E_0` independent of `t` and `P_1, …, P_n` rank-1 projectors; uniqueness is of
   the whole ordered tuple `(E_0, P_1, …, P_n)`, and the equality is of Laurent polynomials.
   The source's `E_0` is "a unitary"; since `det E_P(η) = 1` and `F(η) ∈ SU(2)` for `|η| = 1`,
   any unitary `E_0` in such a decomposition has determinant 1, so `E_0` ranges over `SU(2)`
   (= `P_0 = E_0`, p.4) without changing the statement.
3. If `n ≥ 1`, `F(t) = C_{−n}t^{−n} + ⋯ + C_n t^n`, then the last projector of the decomposition is
   `P_n = C_n† C_n / Tr(C_n† C_n)`. (That `C_n ≠ 0` is proved in the source, p.5, not assumed.) -/
theorem qsp_product_decomposition :
    (∀ (n : ℕ) (P : Fin n → Matrix (Fin 2) (Fin 2) ℂ), (∀ j, IsRankOneProjector (P j)) →
      IsQSPClassE n (List.ofFn fun j => primitiveMatrix (P j)).prod) ∧
    (∀ (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)),
      IsQSPClassE n F → HasQSPDegree n F →
      ∃! D : Matrix.specialUnitaryGroup (Fin 2) ℂ × (Fin n → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j, IsRankOneProjector (D.2 j)) ∧
          F = LaurentPolynomial.C (D.1 : Matrix (Fin 2) (Fin 2) ℂ) *
            (List.ofFn fun j => primitiveMatrix (D.2 j)).prod) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)),
      IsQSPClassE n F → HasQSPDegree n F →
      ∀ (E0 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (P : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j, IsRankOneProjector (P j)) →
        F = LaurentPolynomial.C (E0 : Matrix (Fin 2) (Fin 2) ℂ) *
          (List.ofFn fun j => primitiveMatrix (P j)).prod →
        P ⟨n - 1, by omega⟩ =
          ((F.coeff (n : ℤ))ᴴ * F.coeff (n : ℤ)).trace⁻¹ • ((F.coeff (n : ℤ))ᴴ * F.coeff (n : ℤ))) := by
  sorry

end QAlgorithms.Papers.Haah19
