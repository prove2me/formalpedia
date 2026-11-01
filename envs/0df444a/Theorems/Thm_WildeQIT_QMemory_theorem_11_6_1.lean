-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_6_1
-- name    : WildeQIT.QMemory.theorem_11_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:33.012358+00:00
-- url     : https://prove2.me/theorems/c7e64f04-d11c-4c5f-a2fe-2e08236235d2
-- title:
--   Theorem 11.6.1 — quantum mutual information is non-negative
-- statement:
--   Let $\rho_{AB}$ be any state of a bipartite finite-dimensional quantum system. Then
--
--   $$
--   I(A;B)_\rho=H(A)_\rho+H(B)_\rho-H(AB)_\rho\ge 0 .
--   $$
--
--   Equivalently, quantum entropy is subadditive, $H(A)_\rho+H(B)_\rho\ge H(AB)_\rho$.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.6.1, eq. (11.72), p. 334

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_AFW_qMutualInfo

namespace WildeQIT.QMemory

/-- **Theorem 11.6.1 (Non-Negativity of Quantum Mutual Information)** (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 334). For any bipartite state `ρ_AB`,
`I(A;B)_ρ ≥ 0` (11.72). -/
theorem theorem_11_6_1 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    0 ≤ WildeQIT.AFW.qMutualInfo ρ := by sorry

end WildeQIT.QMemory
