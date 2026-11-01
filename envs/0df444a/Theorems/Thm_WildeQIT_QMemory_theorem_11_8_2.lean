-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_8_2
-- name    : WildeQIT.QMemory.theorem_11_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:04.07353+00:00
-- url     : https://prove2.me/theorems/33a6445f-0577-4f4a-8025-54ce3ce2de8f
-- title:
--   Theorem 11.8.2 — non-negativity of quantum relative entropy, with equality iff $\rho=\sigma$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space with $\mathrm{Tr}\{\sigma\}\le 1$. Then
--
--   $$
--   D(\rho\|\sigma)\ge 0,
--   $$
--
--   and $D(\rho\|\sigma)=0$ if and only if $\rho=\sigma$.
--
--   This is the quantum analogue of Gibbs' inequality, and the source of subadditivity and the other entropy bounds expressed through relative entropy.
--
--   **Formalization Note** $\mathrm{Tr}\{\sigma\}$ is real for positive semi-definite $\sigma$; the hypothesis is stated on its real part.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: Tr{σ} ≤ 1 → (Tr σ).re ≤ 1; reason: the trace of a positive semi-definite matrix is real.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.8.2, eq. (11.119), p. 342

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_qRelEntropy

open scoped ComplexOrder

namespace WildeQIT.QMemory

/-- **Theorem 11.8.2 (Non-Negativity)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 342). For `ρ ∈ D(H)` and positive semi-definite `σ` with `Tr{σ} ≤ 1`,
`D(ρ‖σ) ≥ 0` (11.119), and `D(ρ‖σ) = 0` if and only if `ρ = σ`.

**Formalization Note** `Tr{σ}` is real for positive semi-definite `σ`; the hypothesis is stated
on its real part. -/
theorem theorem_11_8_2 {H : Type} [Fintype H] [DecidableEq H]
    (ρ σ : Matrix H H ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (hσ : σ.PosSemidef)
    (htr : (Matrix.trace σ).re ≤ 1) :
    0 ≤ qRelEntropy ρ σ ∧ (qRelEntropy ρ σ = 0 ↔ ρ = σ) := by sorry

end WildeQIT.QMemory
