-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_4_1
-- name    : WildeQIT.QMemory.theorem_11_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:14.507075+00:00
-- url     : https://prove2.me/theorems/149b490b-c3ea-4256-920e-b84867aa9e76
-- title:
--   Theorem 11.4.1 — conditioning does not increase quantum entropy
-- statement:
--   Let $\rho_{AB}$ be a state of a bipartite finite-dimensional quantum system. Then
--
--   $$
--   H(A)_\rho\ge H(A|B)_\rho ,
--   $$
--
--   where $H(A)_\rho$ is the entropy of $\rho_A=\mathrm{Tr}_B\{\rho_{AB}\}$ and $H(A|B)_\rho=H(AB)_\rho-H(B)_\rho$.
--
--   Conditioning on a system cannot increase entropy, even when the conditioning system is quantum. It is equivalent to subadditivity of quantum entropy.
--
--   **Formalization Note** $\rho_A$ is the published `WildeQIT.partialTraceRight`.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.4.1, eq. (11.51), p. 330

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann
import Definitions.Def_WildeQIT_QMemory_qCondEntropy

namespace WildeQIT.QMemory

/-- **Theorem 11.4.1 (Conditioning Does Not Increase Entropy)** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, p. 330). For a bipartite state `ρ_AB`,
`H(A)_ρ ≥ H(A|B)_ρ` (11.51).

**Formalization Note** `ρ_A = Tr_B{ρ_AB}` is the published `WildeQIT.partialTraceRight`. -/
theorem theorem_11_4_1 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    qCondEntropy ρ ≤ vonNeumann (WildeQIT.partialTraceRight ρ) := by sorry

end WildeQIT.QMemory
