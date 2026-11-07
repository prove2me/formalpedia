-- Prove2me | Theorems.Thm_VecBalPoly_lemma_4_3
-- name    : VecBalPoly.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:16:12.835078+00:00
-- url     : https://prove2.me/theorems/f59b9572-af5b-4146-b266-b982ac4475fb
-- title:
--   Lemma 4.3 — spectral gap $\lambda_1(M)-\lambda_2(M)\ge\eta$ and a positive top eigenvector
-- statement:
--   For every state with $s=|V|>0$ there is a unit eigenvector $v\in\mathbb R^V$ of $M$ for $L=\lambda_1(M)$ that is strictly positive on $V$. If $s\ge2$, the two largest eigenvalues of $M$ satisfy
--   $$\lambda_1(M)-\lambda_2(M)\ge\eta.$$
--
--   The gap makes $L$ a simple eigenvalue, so it is differentiable in the coloring; it controls the eigenvector's motion in Lemma C.1 and Appendix D.
--
--   **Formalization Note** The gap is stated through $v$: every $z\in\mathbb R^V$ orthogonal to $v$ has $z^{\mathsf T}Mz\le(L-\eta)\|z\|_2^2$.
--
--   Differences from the source:
--   - generalization: the matrix M of the algorithm's states → every state with V ≠ ∅ (any T_i, c_i, r_i); reason: the proof uses only that W + ℬ is symmetric and entrywise nonnegative and η > 0, true at every state; the algorithm's states are among these
--   - encoding: λ₁(M) − λ₂(M) ≥ η → z ⬝ Mz ≤ (L − η)‖z‖² for every z supported on V orthogonal to the top eigenvector v; reason: for a top eigenvector v, λ₂ is the maximum of the Rayleigh quotient on v^⊥ (Courant–Fischer)
--   - encoding: v is an eigenvector of M on ℝ^V → (Mv)_j = L v_j for j ∈ V, v vanishing off V; reason: the V × V block of the n × n matrix M
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 4.3, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_VecBalPoly_L

namespace VecBalPoly

open Matrix

/-- **Lemma 4.3 (spectral gap and a positive top eigenvector).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 4.3, p.9 (PDF p.10): "For s ≥ 2, the largest two eigenvalues of M satisfy
λ1(M) − λ2(M) ≥ η. For every s > 0, a unit eigenvector corresponding to L = λ1(M) can be chosen
strictly positive."

**Formalization Note** Stated at every state with `V ≠ ∅` (the lemma has no cleanup
hypothesis). There is a unit vector `v` supported on `V`, strictly positive on `V`, with
`(Mv)ⱼ = Lvⱼ` for `j ∈ V` (an eigenvector of `M` on `ℝ^V` for `L = λ₁`). The gap is stated as:
for `s ≥ 2`, every `z` supported on `V` and orthogonal to `v` has `zᵀMz ≤ (L − η)‖z‖²`. Since
`v` is a top eigenvector, the maximum of the Rayleigh quotient on `v^⊥` is `λ₂(M)`
(Courant–Fischer), so this is `λ₁ − λ₂ ≥ η`. -/
theorem lemma_4_3 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), st.V.Nonempty →
      ∃ v : Fin n → ℝ, (∀ j, j ∉ st.V → v j = 0) ∧ ∑ j, v j ^ 2 = 1 ∧
        (∀ j ∈ st.V, 0 < v j) ∧ (∀ j ∈ st.V, (M A st *ᵥ v) j = L A st * v j) ∧
        (2 ≤ st.V.card → ∀ z : Fin n → ℝ, (∀ j, j ∉ st.V → z j = 0) → z ⬝ᵥ v = 0 →
          z ⬝ᵥ (M A st *ᵥ z) ≤ (L A st - eta n) * ∑ j, z j ^ 2) := by sorry

end VecBalPoly
