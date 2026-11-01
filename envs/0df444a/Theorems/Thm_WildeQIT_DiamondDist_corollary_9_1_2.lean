-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_corollary_9_1_2
-- name    : WildeQIT.DiamondDist.corollary_9_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:02.864104+00:00
-- url     : https://prove2.me/theorems/c667df22-3a91-45ca-aa5f-36b2b9fcc159
-- title:
--   Corollary 9.1.2 (Monotonicity of Trace Distance): $\|\rho_A-\sigma_A\|_1\le\|\rho_{AB}-\sigma_{AB}\|_1$
-- statement:
--   Let $\rho_{AB},\sigma_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$ be density operators on a finite-dimensional bipartite system, and let $\rho_A=\operatorname{Tr}_B\{\rho_{AB}\}$ and $\sigma_A=\operatorname{Tr}_B\{\sigma_{AB}\}$ be their reduced states. The trace distance is monotone under discarding the subsystem $B$:
--
--   $$
--   \|\rho_A-\sigma_A\|_1\le\|\rho_{AB}-\sigma_{AB}\|_1 .
--   $$
--
--   Two states are no easier to distinguish from a part of the system than from the whole; together with isometric invariance this gives monotonicity of the trace distance under every quantum channel (Exercise 9.1.9).
--
--   **Formalization Note** Bipartite operators are matrices indexed by pairs $(i,k)\in a\times b$ (the Kronecker convention), and $\rho_A$ is `WildeQIT.partialTraceRight ρ`.
--
--   Differences from the source:
--   - encoding: $\mathcal H_A\otimes\mathcal H_B$ and $\operatorname{Tr}_B$ → `Matrix (a × b) (a × b) ℂ` and `partialTraceRight`; reason: the book works in finite dimensions; the published partial trace is the book's Definition 4.3.4 in the standard basis
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 9.1.2, p. 258, eq. (9.64)

import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 9.1.2, p. 258.
-/

namespace WildeQIT.DiamondDist

/-- **Corollary 9.1.2 (Monotonicity of Trace Distance)** (Wilde, arXiv:1106.1445v8, p. 258,
eq. (9.64)). For `ρ_AB, σ_AB ∈ D(H_A ⊗ H_B)`, `‖ρ_A − σ_A‖₁ ≤ ‖ρ_AB − σ_AB‖₁`, where
`ρ_A = Tr_B{ρ_AB}` and `σ_A = Tr_B{σ_AB}`.

Formalization Note: bipartite operators are matrices indexed by `a × b`, and `ρ_A` is
`WildeQIT.partialTraceRight ρ` (trace over `B`). -/
theorem corollary_9_1_2 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ σ : Matrix (a × b) (a × b) ℂ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    traceDist (partialTraceRight ρ) (partialTraceRight σ) ≤ traceDist ρ σ := by sorry

end WildeQIT.DiamondDist
