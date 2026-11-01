-- Prove2me | Theorems.Thm_WildeQIT_QMemory_theorem_11_9_5
-- name    : WildeQIT.QMemory.theorem_11_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:51.529787+00:00
-- url     : https://prove2.me/theorems/9b7d2b68-d6ef-48a5-a3b6-e52ddd456a80
-- title:
--   Theorem 11.9.5 — uncertainty principle with quantum memory $H(X|B)_\sigma+H(Z|B)_\tau\ge\log(1/c)+H(A|B)_\rho$
-- statement:
--   Suppose Alice and Bob share a state $\rho_{AB}$ of finite-dimensional systems, and Alice performs either of two POVMs $\{\Lambda^x_A\}$ or $\{\Gamma^z_A\}$ on her share, at least one of which is a rank-one POVM. Let
--
--   $$
--   \sigma_{XB}=\sum_x|x\rangle\langle x|_X\otimes\mathrm{Tr}_A\{(\Lambda^x_A\otimes I_B)\rho_{AB}\},\qquad
--   \tau_{ZB}=\sum_z|z\rangle\langle z|_Z\otimes\mathrm{Tr}_A\{(\Gamma^z_A\otimes I_B)\rho_{AB}\}
--   $$
--
--   be the post-measurement states and $c=\max_{x,z}\|\sqrt{\Lambda^x_A}\sqrt{\Gamma^z_A}\|_\infty^2$ the measurement incompatibility. Then Bob's total uncertainty about the outcomes satisfies
--
--   $$
--   H(X|B)_\sigma+H(Z|B)_\tau\ge\log(1/c)+H(A|B)_\rho .
--   $$
--
--   The bound separates a measurement-dependent term $\log(1/c)$ from a state-dependent term $H(A|B)_\rho$. When $A$ and $B$ share an ebit and Alice measures Pauli $X$ or $Z$, the right-hand side is $1+(-1)=0$ and Bob can predict both outcomes with certainty.
--
--   **Formalization Note** "Rank-one" means every element of the POVM is $|\varphi\rangle\langle\varphi|$ (`HasRankOneElements`), required of at least one of the two POVMs. Logarithms are base 2. For two POVMs on the nonempty system $A$ the incompatibility satisfies $c>0$, so $\log(1/c)$ is the book's quantity.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - reading: rank-one POVM → POVM whose elements are |φ⟩⟨φ| for vectors φ (zero vectors allowed); reason: the book's definition of rank-one POVM (Theorem 11.1.1, p. 323) does not require φ ≠ 0; a zero element contributes a zero block to the post-measurement state and a zero term to c, so it changes neither side.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.9.5, eqs. (11.208)–(11.211), pp. 353–354

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_qCondEntropy
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_QMemory_HasRankOneElements
import Definitions.Def_WildeQIT_QMemory_postMeasState
import Definitions.Def_WildeQIT_QMemory_incompatibility

namespace WildeQIT.QMemory

/-- **Theorem 11.9.5 (Uncertainty Principle with Quantum Memory)** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, p. 354). Alice and Bob share `ρ_AB`; Alice performs
either of the POVMs `{Λ^x_A}` or `{Γ^z_A}` on `A`, at least one of them rank-one. With
`σ_XB`, `τ_ZB` the post-measurement states (11.208)–(11.209) and `c` the incompatibility
(11.210), `H(X|B)_σ + H(Z|B)_τ ≥ log(1/c) + H(A|B)_ρ` (11.211).

**Formalization Note** "Rank-one" is `HasRankOneElements` (every element `|φ⟩⟨φ|`), in a
disjunction. `log` is base 2. `c > 0` for two POVMs on the nonempty system `A`, so `log(1/c)` is
the book's quantity. -/
theorem theorem_11_9_5 {A B X Z : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (Λ : X → Matrix A A ℂ) (Γ : Z → Matrix A A ℂ) (hΛ : IsPOVM Λ) (hΓ : IsPOVM Γ)
    (hrank : HasRankOneElements Λ ∨ HasRankOneElements Γ) :
    Real.logb 2 (1 / incompatibility Λ Γ) + qCondEntropy ρ ≤
      qCondEntropy (postMeasState Λ ρ) + qCondEntropy (postMeasState Γ ρ) := by sorry

end WildeQIT.QMemory
