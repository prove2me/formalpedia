-- Prove2me | Theorems.Thm_WildeQIT_QMemory_corollary_11_9_2
-- name    : WildeQIT.QMemory.corollary_11_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:02.935536+00:00
-- url     : https://prove2.me/theorems/b1bbaeaf-e923-4286-afa1-282391595686
-- title:
--   Corollary 11.9.2 — joint convexity of quantum relative entropy
-- statement:
--   Let $p_X$ be a probability distribution on a finite alphabet $\mathcal X$, $\rho_x$ density operators and $\sigma_x$ positive semi-definite operators on a finite-dimensional Hilbert space for every $x\in\mathcal X$. Set $\rho\equiv\sum_x p_X(x)\rho_x$ and $\sigma\equiv\sum_x p_X(x)\sigma_x$. Then
--
--   $$
--   \sum_x p_X(x)\,D(\rho_x\|\sigma_x)\ge D(\rho\|\sigma).
--   $$
--
--   Joint convexity is one of the equivalent forms of the monotonicity of quantum relative entropy.
--
--   **Formalization Note** The left-hand side is summed in `EReal` with $0\cdot(+\infty)=0$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: Σ_x p_X(x) D(ρ_x‖σ_x) with possibly infinite terms → sum in `EReal` with 0 · (+∞) = 0; reason: the standard convention; an outcome of probability zero does not affect ρ or σ.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 11.9.2, eq. (11.150), p. 346

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_qRelEntropy

open scoped ComplexOrder

namespace WildeQIT.QMemory

/-- **Corollary 11.9.2 (Joint Convexity of Quantum Relative Entropy)** (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 346). For a distribution `p_X` on a finite
alphabet, `ρ_x ∈ D(H)` and positive semi-definite `σ_x`, with `ρ ≡ ∑_x p_X(x) ρ_x` and
`σ ≡ ∑_x p_X(x) σ_x`, `∑_x p_X(x) D(ρ_x‖σ_x) ≥ D(ρ‖σ)` (11.150).

**Formalization Note** The sum on the left is in `EReal`, with `0 · (+∞) = 0` (an outcome of
probability zero contributes nothing). -/
theorem corollary_11_9_2 {X H : Type} [Fintype X] [Fintype H] [DecidableEq H]
    (p : WildeQIT.FinDist X) (ρ σ : X → Matrix H H ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (hσ : ∀ x, (σ x).PosSemidef) :
    qRelEntropy (∑ x, ((p.prob x : ℝ) : ℂ) • ρ x) (∑ x, ((p.prob x : ℝ) : ℂ) • σ x) ≤
      ∑ x, ((p.prob x : ℝ) : EReal) * qRelEntropy (ρ x) (σ x) := by sorry

end WildeQIT.QMemory
