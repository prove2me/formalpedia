-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_1_1
-- name    : WildeQIT.QMemory.theorem_11_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:29.382601+00:00
-- url     : https://prove2.me/theorems/500f96e7-a370-4b18-8944-26072377f3f6
-- title:
--   Theorem 11.1.1 — quantum entropy is the minimal Shannon entropy of a rank-one POVM
-- statement:
--   Let $\rho$ be a density operator on a finite-dimensional Hilbert space $\mathcal H$. Then
--
--   $$
--   H(\rho)=\min_{\{\Lambda_y\}}\Big[-\sum_y\mathrm{Tr}\{\Lambda_y\rho\}\log\mathrm{Tr}\{\Lambda_y\rho\}\Big],
--   $$
--
--   where the minimum is over rank-one POVMs, that is, $\Lambda_y=|\varphi_y\rangle\langle\varphi_y|$ with $\sum_y|\varphi_y\rangle\langle\varphi_y|=I$, with any finite number of outcomes. The minimum is attained.
--
--   The quantum entropy is therefore the least uncertainty about the outcome of a fine-grained measurement of $\rho$: measuring in an eigenbasis is optimal.
--
--   **Formalization Note** "Minimum" is `IsLeast`: $H(\rho)$ is the outcome entropy of some rank-one POVM and a lower bound for all of them. Outcome sets are `Fin m` for every $m$. Logarithms are base 2 with $0\log 0=0$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: minimum over rank-one POVMs with finite outcome sets → `IsLeast` of the set of outcome entropies over POVMs indexed by `Fin m`, every `m`; reason: every finite set is some `Fin m`; `IsLeast` says the minimum exists and equals H(ρ).
--   - reading: rank-one POVM → POVM whose elements are |φ_y⟩⟨φ_y| for vectors φ_y (zero vectors allowed); reason: this is the book's own parenthetical definition, which does not require φ_y ≠ 0; a zero element has probability 0 and contributes 0 log 0 = 0, so the set of values is the same.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.1.1, eq. (11.11), p. 323

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_vonNeumann
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_QMemory_HasRankOneElements

namespace WildeQIT.QMemory

/-- **Theorem 11.1.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 323). For `ρ ∈ D(H)`, `H(ρ) = min_{Λ_y} [−∑_y Tr{Λ_y ρ} log Tr{Λ_y ρ}]` (11.11), the minimum
over rank-one POVMs `Λ_y = |φ_y⟩⟨φ_y|` with `∑_y |φ_y⟩⟨φ_y| = I`.

**Formalization Note** "Minimum" is `IsLeast`: `H(ρ)` is the Shannon entropy (bits) of some
rank-one POVM's outcome distribution, and a lower bound for all of them. The outcome set is any
finite set, written `Fin m` for every `m`. `Tr{Λ_y ρ}` is taken as a real number (real part). -/
theorem theorem_11_1_1 {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    IsLeast {h : ℝ | ∃ (m : ℕ) (Λ : Fin m → Matrix A A ℂ),
        IsPOVM Λ ∧ HasRankOneElements Λ ∧
        h = -∑ y, (Matrix.trace (Λ y * ρ)).re * Real.logb 2 (Matrix.trace (Λ y * ρ)).re}
      (vonNeumann ρ) := by sorry

end WildeQIT.QMemory
