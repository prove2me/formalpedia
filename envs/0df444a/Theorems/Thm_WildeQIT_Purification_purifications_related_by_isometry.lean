-- Prove2me | Theorems.Thm_WildeQIT_Purification_purifications_related_by_isometry
-- name    : WildeQIT.Purification.purifications_related_by_isometry
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:42.913232+00:00
-- url     : https://prove2.me/theorems/b404b5a7-5435-4e4c-ab76-e95eb64d4331
-- title:
--   All purifications of a density operator are related by an isometry on the purifying system (Theorem 5.1.1)
-- statement:
--   Let $\rho_A$ be a density operator on a finite-dimensional Hilbert space $\mathcal H_A$, and let $|\psi\rangle_{R_1A}\in\mathcal H_{R_1}\otimes\mathcal H_A$ and $|\phi\rangle_{R_2A}\in\mathcal H_{R_2}\otimes\mathcal H_A$ be purifications of $\rho_A$:
--
--   $$
--   \operatorname{Tr}_{R_1}\{|\psi\rangle\langle\psi|_{R_1A}\} = \rho_A = \operatorname{Tr}_{R_2}\{|\phi\rangle\langle\phi|_{R_2A}\},
--   $$
--
--   with $\dim\mathcal H_{R_1}\le\dim\mathcal H_{R_2}$. Then there exists an isometry $U_{R_1\to R_2}$ ($U^\dagger U = I_{R_1}$, the book's Definition 4.6.3) such that
--
--   $$
--   |\phi\rangle_{R_2A} = (U_{R_1\to R_2}\otimes I_A)\,|\psi\rangle_{R_1A}.
--   $$
--
--   Purifications are thus unique up to an isometry acting only on the purifying system. This is the basic tool for moving between purifications of the same state, for example in proofs about isometric extensions of channels and in Uhlmann's theorem.
--
--   **Formalization Note** Vectors are functions on product bases with the reference system as the left factor; $\operatorname{Tr}_R$ is `WildeQIT.partialTraceLeft` and $U\otimes I_A$ is the Kronecker product `U ⊗ₖ 1`. The isometry is an $R_2\times R_1$ matrix satisfying the published predicate `HarlowTASI.IsIsometry` ($U^\dagger U = 1$).
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces $\mathcal H_{R_1},\mathcal H_{R_2},\mathcal H_A$ and vectors in $\mathcal H_R\otimes\mathcal H_A$ → finite index types `R1`, `R2`, `a` and functions on `R × a`, reference first; reason: Lean convention for a chosen orthonormal basis; same objects.
--   - encoding: "let $\rho_A$ be a density operator" as a separate hypothesis → no separate hypothesis; reason: `IsPurification ρ ψ` (a unit vector with reduced state $\rho$) already forces $\rho$ to be positive semidefinite with unit trace, so no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 5.1.1, eq. (5.5), p. 185

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics
import Definitions.Def_WildeQIT_Purification_IsPurification

open scoped Matrix Kronecker

namespace WildeQIT.Purification

/-- **Theorem 5.1.1 (all purifications are related by an isometry on the purifying system).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 5.1.1, p. 185:
"let ρ_A be a density operator, and let |ψ⟩_{R1A} and |ϕ⟩_{R2A} be purifications of ρ_A, such that
dim(H_{R1}) ≤ dim(H_{R2}). Then there exists an isometry U_{R1→R2} such that
|ϕ⟩_{R2A} = (U_{R1→R2} ⊗ I_A)|ψ⟩_{R1A}." (5.5)

`ψ : R1 × a → ℂ` and `φ : R2 × a → ℂ` are purifications of the same `ρ` (reference first),
`card R1 ≤ card R2`, and the conclusion is an isometry `U : Matrix R2 R1 ℂ`
(`HarlowTASI.IsIsometry U`, i.e. `Uᴴ U = 1`, the book's Definition 4.6.3, p. 162) with
`φ = (U ⊗ₖ I_A) ψ`.

**Formalization Note.** `ρ` being a density operator is implied by `IsPurification ρ ψ` (a
unit vector's reduced state has unit trace and is positive semidefinite), so it is not a
separate hypothesis. Hilbert spaces are finite-dimensional, with bases indexed by finite types. -/
theorem purifications_related_by_isometry {a R1 R2 : Type} [Fintype a] [DecidableEq a]
    [Fintype R1] [DecidableEq R1] [Fintype R2]
    (ρ : Matrix a a ℂ) (ψ : R1 × a → ℂ) (φ : R2 × a → ℂ)
    (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ)
    (hdim : Fintype.card R1 ≤ Fintype.card R2) :
    ∃ U : Matrix R2 R1 ℂ, HarlowTASI.IsIsometry U ∧ φ = (U ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ ψ := by sorry

end WildeQIT.Purification
