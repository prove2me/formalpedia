-- Prove2me | Theorems.Thm_ProConChoice_Rational_rs_cs_matrix_tu
-- name    : ProConChoice.Rational.rs_cs_matrix_tu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:36.563998+00:00
-- url     : https://prove2.me/theorems/e475460d-94f4-4e60-a73a-a86d61496ea6
-- title:
--   §7, p. 23 — the coefficient matrix of the system (RS)–(CS) is totally unimodular
-- statement:
--   Let $I$ and $J$ be finite index sets. Consider the linear system in the unknowns $\lambda_{ij}$, $(i, j) \in I \times J$, consisting of the row equations $\sum_{j \in J} \lambda_{ij} = r_i$ for $i \in I$ (RS) and the column equations $\sum_{i \in I} \lambda_{ij} = c_j$ for $j \in J$ (CS). Its coefficient matrix has one row for each $i \in I$, with a $1$ in the columns $(i, j)$, $j \in J$, and one row for each $j \in J$, with a $1$ in the columns $(i, j)$, $i \in I$, and zeros elsewhere. This matrix is totally unimodular:
--   $$\text{every square submatrix has determinant } 0, 1 \text{ or } -1.$$
--
--   In Section 7, $I$ indexes the $k!$ prefixes ordering $X \setminus S$ and $J$ the alternatives of $S$; total unimodularity together with Lemma 4 makes the weights of the next step integral.
--
--   **Formalization Note** The matrix is indexed by rows `I ⊕ J` and columns `I × J`. The paper's description of the rows by integer indices on p. 23 does not match its own column ordering; the matrix stated here is the coefficient matrix of (RS)–(CS) that the text describes in words.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 23, Section 7 (proof of Theorem 1), total unimodularity of the matrix defining (RS) and (CS)

import Mathlib

namespace ProConChoice.Rational

/-- Section 7 (p. 23): the coefficient matrix of the system (RS)–(CS) is totally unimodular. Its
columns are the variables `λᵢⱼ`, `(i, j) ∈ I × J`; the row of `i ∈ I` (RS) has a `1` exactly in the
columns `(i, j)`, `j ∈ J`, and the row of `j ∈ J` (CS) has a `1` exactly in the columns `(i, j)`,
`i ∈ I`. -/
theorem rs_cs_matrix_tu {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    (Matrix.of (fun (r : I ⊕ J) (c : I × J) =>
      Sum.elim (fun i => if c.1 = i then (1 : ℝ) else 0)
        (fun j => if c.2 = j then (1 : ℝ) else 0) r)).IsTotallyUnimodular := by sorry

end ProConChoice.Rational
