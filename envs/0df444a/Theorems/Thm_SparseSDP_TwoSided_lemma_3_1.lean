-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_3_1
-- name    : SparseSDP.TwoSided.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:10.007863+00:00
-- url     : https://prove2.me/theorems/b76dc80f-c7c5-4f85-bc3b-b181bfdf3f44
-- title:
--   Lemma 3.1, pp. 22–23 — the coordinate-sampling estimator is unbiased with operator-norm second moment
-- statement:
--   Let $A$ be Hermitian with $\|A\|\le\omega$, let $\psi$ be a unit vector, and sample $I$ with $P[I=i]=|[\psi]_i|^2$. Then
--
--   1. $\mathbb E_I[Z_A(\psi,I)]=\psi^\dagger A\psi$;
--   2. $\mathbb E_I[Z_A(\psi,I)^2]\le\|A\psi\|_2^2\le\omega^2$.
--
--   The second moment is governed by the operator norm rather than the Frobenius norm, which is what lets one coordinate serve every constraint.
--
--   Differences from the source:
--   - generalization: $A\in\mathbb C^{n\times n}$ → any `RCLike` scalar field; reason: Algorithm 7 uses the real case; it specializes to $\mathbb C$
--   - encoding: $\mathbb E_I$ → the finite sum $\sum_i|[\psi]_i|^2(\cdot)$; reason: definition of the expectation for this law
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 3.1, pp. 22–23

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_gap
import Definitions.Def_SparseSDP_TwoSided_zHat

open Matrix
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Lemma 3.1** (Moments of the Coordinate-Sampling Estimator), pp. 22–23.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 3.1, pp. 22–23.

`E_I[f(I)]` for `P[I = i] = |[ψ]ᵢ|²` is the finite sum `∑ᵢ |[ψ]ᵢ|² f(i)`. -/
theorem lemma_3_1 {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (ψ : Fin n → 𝕜)
    (ω : ℝ) (hA : A.IsHermitian) (hω : ‖A‖ ≤ ω) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    ∑ i, ‖ψ i‖ ^ 2 * zEst A ψ i = RCLike.re (star ψ ⬝ᵥ (A *ᵥ ψ)) ∧
    ∑ i, ‖ψ i‖ ^ 2 * zEst A ψ i ^ 2 ≤ l2 (A *ᵥ ψ) ^ 2 ∧
    l2 (A *ᵥ ψ) ^ 2 ≤ ω ^ 2 := by sorry

end SparseSDP.TwoSided
