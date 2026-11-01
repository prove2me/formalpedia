-- Prove2me | Theorems.Thm_WildeQIT_QMemory_proposition_11_8_2
-- name    : WildeQIT.QMemory.proposition_11_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:03.046043+00:00
-- url     : https://prove2.me/theorems/7b609c88-62b4-4491-8d5e-052c67b99928
-- title:
--   Proposition 11.8.2 — $\sigma\le\sigma'$ implies $D(\rho\|\sigma')\le D(\rho\|\sigma)$
-- statement:
--   Let $\rho$ be a density operator and $\sigma,\sigma'$ positive semi-definite operators on a finite-dimensional Hilbert space with $\sigma\le\sigma'$ (that is, $\sigma'-\sigma$ is positive semi-definite). Then
--
--   $$
--   D(\rho\|\sigma')\le D(\rho\|\sigma).
--   $$
--
--   Enlarging the second argument in the operator order can only decrease the relative entropy. The proof of the uncertainty principle with quantum memory uses this step to bring in the incompatibility $c$.
--
--   **Formalization Note** The comparison is in `EReal`; $\sigma\le\sigma'$ is the Loewner order.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 11.8.2, eq. (11.140), p. 344

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_qRelEntropy

open scoped ComplexOrder

namespace WildeQIT.QMemory

/-- **Proposition 11.8.2** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 344). For `ρ ∈ D(H)` and positive semi-definite `σ, σ′` with `σ ≤ σ′`,
`D(ρ‖σ′) ≤ D(ρ‖σ)` (11.140).

**Formalization Note** `σ ≤ σ′` is the Loewner order: `σ′ − σ` is positive semi-definite. -/
theorem proposition_11_8_2 {H : Type} [Fintype H] [DecidableEq H]
    (ρ σ σ' : Matrix H H ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (hσ : σ.PosSemidef)
    (hσ' : σ'.PosSemidef) (hle : (σ' - σ).PosSemidef) :
    qRelEntropy ρ σ' ≤ qRelEntropy ρ σ := by sorry

end WildeQIT.QMemory
