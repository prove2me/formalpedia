-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_2_2
-- name    : WildeQIT.QMemory.theorem_11_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:50.553893+00:00
-- url     : https://prove2.me/theorems/5ddc1aee-5fdb-4781-836e-64c213656775
-- title:
--   Theorem 11.2.2 — joint entropy of a classical–quantum state
-- statement:
--   Let $p_X$ be a probability distribution on a finite alphabet $\mathcal X$ and $\{\rho^x_B\}$ density operators on $\mathcal H_B$, and let $\rho_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_B$ be the classical–quantum state (11.32). Then
--
--   $$
--   H(XB)_\rho=H(X)+\sum_x p_X(x)\,H(\rho^x_B),
--   $$
--
--   where $H(X)=-\sum_x p_X(x)\log p_X(x)$ is the Shannon entropy of $p_X$.
--
--   This identity gives $H(B|X)_\rho=\sum_x p_X(x)H(\rho^x_B)$: when the conditioning system is classical, conditional quantum entropy behaves as in the classical case.
--
--   **Formalization Note** $H(X)$ is the published `WildeQIT.entropy` (bits) and $p_X$ the published `WildeQIT.FinDist`.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: ρ^x_B states (Definition 4.3.5) → hypothesis that every ρ^x_B is a density operator; reason: same assumption, written as a binder.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.2.2, eqs. (11.32)–(11.33), pp. 326–327

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_vonNeumann
import Definitions.Def_WildeQIT_QMemory_cqState

namespace WildeQIT.QMemory

/-- **Theorem 11.2.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 327). The joint entropy of the classical–quantum state
`ρ_XB = ∑_x p_X(x) |x⟩⟨x|_X ⊗ ρ^x_B` (11.32) is `H(XB)_ρ = H(X) + ∑_x p_X(x) H(ρ^x_B)` (11.33).

**Formalization Note** Each `ρ^x_B` is a density operator (Definition 4.3.5); `H(X)` is the
published Shannon entropy `WildeQIT.entropy` in bits. -/
theorem theorem_11_2_2 {X B : Type} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
    (p : WildeQIT.FinDist X) (ρ : X → Matrix B B ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) :
    vonNeumann (cqState p ρ) = WildeQIT.entropy p + ∑ x, p.prob x * vonNeumann (ρ x) := by sorry

end WildeQIT.QMemory
