-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_lemma_9_1_2
-- name    : WildeQIT.DiamondDist.lemma_9_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:06.703988+00:00
-- url     : https://prove2.me/theorems/adb37251-52cf-4ab7-b50f-a7f0983397ee
-- title:
--   Lemma 9.1.2 (Triangle Inequality): $\|\rho-\sigma\|_1\le\|\rho-\tau\|_1+\|\tau-\sigma\|_1$
-- statement:
--   For any three density operators $\rho,\sigma,\tau\in\mathcal D(\mathcal H)$ on a finite-dimensional Hilbert space,
--
--   $$
--   \|\rho-\sigma\|_1\le\|\rho-\tau\|_1+\|\tau-\sigma\|_1 .
--   $$
--
--   The trace distance between states thus obeys the triangle inequality, which is what makes errors of successive approximation steps add up in coding proofs.
--
--   Differences from the source:
--   - encoding: states on $\mathcal H$ → `Matrix n n ℂ` over a finite index type; reason: the book works in finite dimensions
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.1.2, p. 257, eq. (9.52)

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 9.1.2, p. 257.
-/

namespace WildeQIT.DiamondDist

/-- **Lemma 9.1.2 (Triangle Inequality)** (Wilde, arXiv:1106.1445v8, p. 257, eq. (9.52)).
For any three quantum states `ρ, σ, τ ∈ D(H)`, `‖ρ − σ‖₁ ≤ ‖ρ − τ‖₁ + ‖τ − σ‖₁`. -/
theorem lemma_9_1_2 {n : Type} [Fintype n] [DecidableEq n] (ρ σ τ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hτ : IsDensityOperator τ) :
    traceDist ρ σ ≤ traceDist ρ τ + traceDist τ σ := by sorry

end WildeQIT.DiamondDist
