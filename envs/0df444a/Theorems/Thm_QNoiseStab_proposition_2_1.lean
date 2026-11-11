-- Prove2me | Theorems.Thm_QNoiseStab_proposition_2_1
-- name    : QNoiseStab.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:20:55.152201+00:00
-- url     : https://prove2.me/theorems/6406af3e-a4c9-4b8d-b18e-e44d196dd403
-- title:
--   Proposition 2.1 — Perron–Frobenius: $\min_i r_i\le\lambda_{\max}(M)\le\max_i r_i$
-- statement:
--   Let $N\ge1$ and let $M\in\mathbb R^{N\times N}$ be symmetric with $M_{ij}\ge0$ for all $i,j$. Write $r_i=\sum_{j=1}^N M_{ij}$ for the row sums and $\lambda_{\max}(M)$ for the largest eigenvalue of $M$. Then
--
--   $$
--   \min_{i\in[N]} r_i\ \le\ \lambda_{\max}(M)\ \le\ \max_{i\in[N]} r_i ,
--   $$
--
--   and in particular, if every row sum equals $r$, then $\lambda_{\max}(M)=r$.
--
--   In the proof of Theorem 3.4 this bounds the norm of the compressed noise operator $\Pi_E T_p^A \Pi_E$ by its largest row sum $\max_{x\in E}\Pr[N_p^A(x)\in E]$.
--
--   **Formalization Note** $\lambda_{\max}$ is the maximum of the real eigenvalues of the Hermitian (= symmetric) real matrix $M$.
--
--   Differences from the source:
--   - encoding: $M\in\mathbb R^{N\times N}$ with minima and maxima over $[N]$ → `M : Matrix (Fin N) (Fin N) ℝ` with `0 < N`; reason: min and max over $[N]$ are undefined for $N=0$; indices are 0-based
--   - encoding: $M$ symmetric; $\lambda_{\max}(M)$ → `M.IsHermitian`; the `Finset.sup'` of `hM.eigenvalues`; reason: for a real matrix Hermitian means symmetric, and its eigenvalues are real
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Proposition 2.1, p.5

import Mathlib

namespace QNoiseStab

/-- **Proposition 2.1** (Perron–Frobenius; Beame–Holman–Kornerup, *A Noise Operator Approach to
Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of
2026-11-02, sha256 814fe20e…), p.5). Let `M ∈ ℝ^{N×N}` be symmetric and entrywise nonnegative, and
let `r_i = Σ_j M_ij`. Then `min_i r_i ≤ λ_max(M) ≤ max_i r_i`; in particular, if every row sum
equals `r`, then `λ_max(M) = r`.

**Formalization Note** Symmetry of a real matrix is `M.IsHermitian`; `λ_max(M)` is the largest of
its (real) eigenvalues `hM.eigenvalues`, a `Finset.sup'` over the nonempty index `Fin N`
(`0 < N`, since `min` and `max` over `[N]` are undefined for `N = 0`). Indices are 0-based. -/
theorem proposition_2_1 {N : ℕ} (hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j) :
    let hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    let r : Fin N → ℝ := fun i => ∑ j, M i j
    let lamMax : ℝ := Finset.univ.sup' hne hM.eigenvalues
    (Finset.univ.inf' hne r ≤ lamMax ∧ lamMax ≤ Finset.univ.sup' hne r) ∧
      ∀ c : ℝ, (∀ i, r i = c) → lamMax = c := by sorry

end QNoiseStab
