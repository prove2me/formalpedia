-- Prove2me | Theorems.Thm_SetOptLattice_Existence_proposition_3_9
-- name    : SetOptLattice.Existence.proposition_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:49.147577+00:00
-- url     : https://prove2.me/theorems/59138514-0645-46e1-bb2a-fca571bde2f7
-- title:
--   Proposition 3.9, p. 17 — for every ε > 0 an (ε,Ψ)-solution of (P) exists
-- statement:
--   Let $(Z,\preceq)$ be a preordered set, $\Psi$ a non-empty family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$, $X$ a non-empty set and $f\colon X\to\mathcal P(Z,\Psi)$. Then for every $\varepsilon>0$ the problem
--
--   $$\text{minimize } f(x)\ \text{ over } x\in X \tag{P}$$
--
--   has an $(\varepsilon,\Psi)$-solution: a non-empty set $M\subseteq X$ which is an $(\varepsilon,\Psi)$-infimizer of $f$ and consists of $(\varepsilon,\Psi)$-minimizers of $f$.
--
--   As in scalar optimization, approximate solutions exist without any compactness or semicontinuity assumption.
--
--   **Formalization Note** The hypothesis $\Psi\neq\emptyset$ is added: for $\Psi=\emptyset$ there are no $(\varepsilon,\Psi)$-minimizers, so no non-empty set of them exists, and the statement is false. $X\neq\emptyset$ is the paper's standing assumption (Definition 2.17, p. 13).
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 17, Proposition 3.9

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Proposition 3.9, p. 17: for `ε > 0` an `(ε, Ψ)`-solution of (P) exists. -/
theorem proposition_3_9 {X Z : Type*} [Nonempty X] [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : Set X, IsSolution Ψ f ε M := by sorry

end SetOptLattice.Existence
