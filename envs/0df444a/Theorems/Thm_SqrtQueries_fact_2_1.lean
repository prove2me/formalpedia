-- Prove2me | Theorems.Thm_SqrtQueries_fact_2_1
-- name    : SqrtQueries.fact_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:28:53.362444+00:00
-- url     : https://prove2.me/theorems/8efb342f-88d5-4067-99b1-9ed1c665c990
-- title:
--   Fact 2.1 — square roots of a matrix with simple spectrum
-- statement:
--   Let $U=W\Lambda W^\dagger$ where $W$ is unitary and $\Lambda=\operatorname{diag}(\lambda_i)$ has pairwise distinct diagonal entries (a simple spectrum, the standing assumption of Section 2.1). Let $\Lambda^{1/2}$ be any matrix with $(\Lambda^{1/2})^2=\Lambda$. Then:
--
--   1. the square roots of $U$, that is, the matrices $V$ with $V^2=U$, are exactly the matrices
--   $$
--   V=W\,\Sigma\,\Lambda^{1/2}\,W^\dagger,
--   $$
--   where $\Sigma$ is any diagonal matrix with entries $\pm1$;
--   2. for every square root $V$ of $U$, a nonzero vector is an eigenvector of $V$ if and only if it is an eigenvector of $U$.
--
--   So the eigenvalues of a square root are determined up to a sign, and its eigenvectors are those of $U$.
--
--   **Formalization Note** $\Lambda^{1/2}$ is an arbitrary matrix squaring to $\Lambda$, not assumed diagonal, and a square root is any complex matrix $V$ with $V V=U$.
--
--   Differences from the source:
--   - generalization: U a unitary with simple spectrum → U = WΛW† with W unitary and Λ diagonal with distinct entries, not necessarily of modulus one; reason: the statement and its proof do not use |λ_i| = 1; unitary U is the case |λ_i| = 1
--   - reading: the eigenvectors of U and its square roots are the same → for every V with V² = U and every nonzero v: v is an eigenvector of V iff it is an eigenvector of U; reason: the natural meaning of equal eigenvector sets
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Fact 2.1, p.10

import Mathlib

namespace SqrtQueries

open Matrix

/-- **Fact 2.1** of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.10. Let `U = W Λ W†` with `W` unitary and `Λ = diag(λ)` with simple
spectrum (the `λ_i` pairwise distinct), and let `Λ^{1/2}` be any matrix with `(Λ^{1/2})² = Λ`.
Then (a) the square roots of `U` are exactly the matrices `W Σ Λ^{1/2} W†` with `Σ` a diagonal
matrix of `±1`s, and (b) for every square root `V` of `U`, a nonzero vector is an eigenvector
of `V` if and only if it is an eigenvector of `U`.

**Formalization Note.** Section 2.1 assumes simple spectra throughout ("we will suppose our
unitaries have simple spectra"); this is `Function.Injective lam`. The eigenvalues are not
required to have modulus one, so `U` need not be unitary (a generalization). `Λ^{1/2}` is any
matrix `L` with `L * L = Λ`, not assumed diagonal, and a square root is any complex matrix
`V` with `V * V = U`. -/
theorem fact_2_1 {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (lam : n → ℂ) (hlam : Function.Injective lam)
    (L : Matrix n n ℂ) (hL : L * L = Matrix.diagonal lam) (U : Matrix n n ℂ)
    (hU : U = W * Matrix.diagonal lam * Wᴴ) :
    (∀ V : Matrix n n ℂ, V * V = U ↔
      ∃ σ : n → ℂ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ V = W * Matrix.diagonal σ * L * Wᴴ) ∧
    (∀ V : Matrix n n ℂ, V * V = U → ∀ v : n → ℂ, v ≠ 0 →
      ((∃ μ : ℂ, V *ᵥ v = μ • v) ↔ (∃ c : ℂ, U *ᵥ v = c • v))) := by sorry

end SqrtQueries
