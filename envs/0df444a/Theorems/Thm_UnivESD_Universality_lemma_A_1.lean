-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_A_1
-- name    : UnivESD.Universality.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:29.129141+00:00
-- url     : https://prove2.me/theorems/a38b771d-2114-4d9d-8573-6ec9a1ace564
-- title:
--   Lemma A.1 (Cauchy's interlacing law): $\sigma_i(A)\ge\sigma_i(A')\ge\sigma_{i+k}(A)$
-- statement:
--   Let $A$ be an $n\times n$ complex matrix and let $A'$ be the $(n-k)\times n$ submatrix formed by its first $m:=n-k$ rows. Let $\sigma_1(A)\ge\cdots\ge\sigma_n(A)\ge0$ be the singular values of $A$, and similarly for $A'$. Then
--   $$\sigma_i(A)\ge\sigma_i(A')\ge\sigma_{i+k}(A)\qquad\text{for every }1\le i\le n-k.$$
--
--   Deleting rows can only decrease singular values, and by no more than a shift of the index by the number of deleted rows. The paper uses it to compare the singular values of $A_n$ with those of its first $n'$ rows.
--
--   **Formalization Note.** Singular values are one-based; the $n-k$ singular values of $A'$ are the first $n-k$ of Mathlib's singular values of $A'$ acting $\mathbb C^n\to\mathbb C^{n-k}$. Natural-number subtraction: when $k>n$ the range of $i$ is empty.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2057 (PDF 35), Lemma A.1

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma A.1 (Cauchy's interlacing law for singular values), p. 2057. `A'` is the
`(n - k) × n` submatrix of the first `n - k` rows of `A`; singular values are one-based. -/
theorem lemma_A_1 (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (hi : 1 ≤ i)
    (hik : i ≤ n - k) :
    singVal (A.submatrix (Fin.castLE (Nat.sub_le n k)) id) i ≤ singVal A i ∧
      singVal A (i + k) ≤ singVal (A.submatrix (Fin.castLE (Nat.sub_le n k)) id) i := by sorry

end UnivESD.Universality
