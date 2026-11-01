-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_lemma_9_1_1
-- name    : WildeQIT.DiamondDist.lemma_9_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:00.565612+00:00
-- url     : https://prove2.me/theorems/fea2980b-16ff-4eb1-be3a-e7ee94f7c1e1
-- title:
--   Lemma 9.1.1: $\tfrac12\|\rho-\sigma\|_1=\max_{0\le\Lambda\le I}\operatorname{Tr}\{\Lambda(\rho-\sigma)\}$
-- statement:
--   Let $\rho,\sigma\in\mathcal D(\mathcal H)$ be density operators (positive semi-definite, unit trace) on a finite-dimensional Hilbert space $\mathcal H$. The normalized trace distance equals the largest probability difference that $\rho$ and $\sigma$ can give to the same measurement outcome $\Lambda$:
--
--   $$
--   \tfrac12\|\rho-\sigma\|_1=\max_{0\le\Lambda\le I}\operatorname{Tr}\{\Lambda(\rho-\sigma)\},
--   $$
--
--   the maximum being over all positive semi-definite $\Lambda\in\mathcal L(\mathcal H)$ with eigenvalues at most one. In particular the maximum is attained.
--
--   This is the characterization behind the operational meaning of the trace distance (optimal success probability of distinguishing two states) and the proofs of Lemma 9.1.2 and Corollaries 9.1.1, 9.1.2.
--
--   **Formalization Note** $0\le\Lambda\le I$ is written as $\Lambda\succeq0$ and $I-\Lambda\succeq0$, which is equivalent to "positive semi-definite with eigenvalues bounded by one". The trace $\operatorname{Tr}\{\Lambda(\rho-\sigma)\}$ is real for such $\Lambda$; Lean takes the real part of the complex trace. `traceDist ρ σ` is the unnormalized $\|\rho-\sigma\|_1$.
--
--   Differences from the source:
--   - encoding: $\max_{0\le\Lambda\le I}$ → `IsGreatest` of $\{\operatorname{Re}\operatorname{Tr}\{\Lambda(\rho-\sigma)\} : \Lambda\succeq0,\ I-\Lambda\succeq0\}$; reason: states that the maximum exists and equals $\frac12\|\rho-\sigma\|_1$; the trace is real on this set
--   - encoding: states on $\mathcal H$ → `Matrix n n ℂ` over a finite index type; reason: the book works in finite dimensions
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.1.1, p. 254, eq. (9.27)

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 9.1.1, p. 254.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.DiamondDist

/-- **Lemma 9.1.1** (Wilde, arXiv:1106.1445v8, p. 254, eq. (9.27)). For quantum states
`ρ, σ ∈ D(H)`, `(1/2)‖ρ − σ‖₁ = max_{0 ≤ Λ ≤ I} Tr{Λ(ρ − σ)}`, the maximization being over
all positive semi-definite `Λ ∈ L(H)` with eigenvalues bounded from above by one.

Formalization Note: `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `Tr{Λ(ρ − σ)}` is
real for such `Λ` and is taken as the real part of the complex trace. The maximum is stated as
`IsGreatest` (attained, and an upper bound). -/
theorem lemma_9_1_1 {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    IsGreatest {x : ℝ | ∃ Λ : Matrix n n ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧ x = (Λ * (ρ - σ)).trace.re} ((1 / 2 : ℝ) * traceDist ρ σ) := by sorry

end WildeQIT.DiamondDist
