-- Prove2me | Theorems.Thm_SqrtQueries_lemma_3_8
-- name    : SqrtQueries.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:28:59.187217+00:00
-- url     : https://prove2.me/theorems/ab275cfc-15a0-473e-abe6-4efbfbd256c3
-- title:
--   Lemma 3.8 (Hadamard formula) — $R^{(k)}(t)=[iA,R(t)]_k$
-- statement:
--   Let $A$ and $R$ be complex square matrices of the same size, and let $R(t)=e^{itA}Re^{-itA}$ for real $t$. For every integer $k\ge0$,
--   $$
--   R^{(k)}(t)=[iA,R(t)]_k ,
--   $$
--   where $[X,Z]=XZ-ZX$ is the commutator and $[X,Z]_k$ the nested commutator: $[X,Z]_0=Z$ and $[X,Z]_k=[X,[X,Z]_{k-1}]$ for $k\ge1$.
--
--   The cases $k=1,2$ give the first and second derivative of the conjugation $t\mapsto e^{itA}Re^{-itA}$ used in the Taylor expansion of Proposition 3.6.
--
--   **Formalization Note** $R^{(k)}$ is the $k$-th iterated derivative of a function $\mathbb R\to\mathbb C^{n\times n}$; the derivative does not depend on the norm on this finite-dimensional space (the operator norm is used).
--
--   Differences from the source:
--   - reading: t (domain unstated) → t ∈ ℝ; reason: the lemma is applied for real t ∈ [0, 1/4] in the proof of Proposition 3.6
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Lemma 3.8, p.18

import Mathlib

open scoped Matrix.Norms.L2Operator

namespace SqrtQueries

/-- **Lemma 3.8** (Hadamard formula) of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.18: for square matrices `A`, `R` of the same size and
`R(t) = e^{itA} R e^{−itA}`, for every integer `k ≥ 0`, `R^{(k)}(t) = [iA, R(t)]_k`, the `k`-fold
nested commutator (`[X, Z]_0 = Z`, `[X, Z]_k = [X, [X, Z]_{k−1}]`, `[X, Z] = XZ − ZX`).

**Formalization Note.** `t` is real and `R^{(k)}` is the `k`-th derivative (`iteratedDeriv`) of a
function `ℝ → Matrix n n ℂ`; the nested commutator is the `k`-th iterate of
`Z ↦ (iA)Z − Z(iA)`. The exponential is `NormedSpace.exp`. The derivative is taken for the
normed structure `Matrix.Norms.L2Operator`; all norms on a finite-dimensional space give the
same derivative. `A` and `R` are arbitrary complex square matrices, as on the page. -/
theorem lemma_3_8 {n : Type*} [Fintype n] [DecidableEq n] (A R : Matrix n n ℂ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => NormedSpace.exp (((s : ℂ) * Complex.I) • A) * R *
        NormedSpace.exp ((-((s : ℂ) * Complex.I)) • A)) t =
      (fun Z => (Complex.I • A) * Z - Z * (Complex.I • A))^[k]
        (NormedSpace.exp (((t : ℂ) * Complex.I) • A) * R *
          NormedSpace.exp ((-((t : ℂ) * Complex.I)) • A)) := by sorry

end SqrtQueries
