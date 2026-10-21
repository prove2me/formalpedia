-- Prove2me | Theorems.Thm_SetOptLattice_Existence_proposition_2_3
-- name    : SetOptLattice.Existence.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:40.67798+00:00
-- url     : https://prove2.me/theorems/d35fd682-8099-43c2-a34e-9be5955512a2
-- title:
--   Proposition 2.3, p. 4 — on P(Z,Ψ), ⪯_Ψ is ⊇, and (P(Z,Ψ),⊇) is a complete lattice with inf 𝒜 = cl_Ψ ⋃𝒜, sup 𝒜 = ⋂𝒜
-- statement:
--   Let $(Z,\preceq)$ be a preordered set, $\Psi$ a family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$, and $\mathcal P(Z,\Psi)=\{D\subseteq Z\mid D=\operatorname{cl}_\Psi D\}$ the Ψ-closed sets. Then:
--
--   1. for $D,E\in\mathcal P(Z,\Psi)$, $\;D\preceq_\Psi E\iff D\supseteq E$;
--   2. for every $\mathcal A\subseteq\mathcal P(Z,\Psi)$ the set
--   $$B=\operatorname{cl}_\Psi\bigcup_{A\in\mathcal A}A$$
--   belongs to $\mathcal P(Z,\Psi)$, contains every $A\in\mathcal A$, and is contained in every $C\in\mathcal P(Z,\Psi)$ that contains every $A\in\mathcal A$; that is, $B=\inf\mathcal A$ with respect to $\supseteq$;
--   3. for every $\mathcal A\subseteq\mathcal P(Z,\Psi)$ the set $\bigcap_{A\in\mathcal A}A$ belongs to $\mathcal P(Z,\Psi)$, is contained in every $A\in\mathcal A$, and contains every $C\in\mathcal P(Z,\Psi)$ contained in every $A\in\mathcal A$; that is, it is $\sup\mathcal A$ with respect to $\supseteq$.
--
--   Items 2 and 3 say that $(\mathcal P(Z,\Psi),\supseteq)$ is a complete lattice with the stated infimum and supremum. This is the image space in which the set optimization problem (P) is posed.
--
--   **Formalization Note** "Complete lattice" is stated through its content: every subfamily of $\mathcal P(Z,\Psi)$, including the empty one, has a greatest lower bound and a least upper bound in $(\mathcal P(Z,\Psi),\supseteq)$, given by the displayed formulas. No `CompleteLattice` instance is built.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 4, Proposition 2.3

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Proposition 2.3, p. 4: on `P(Z, Ψ)` the relation `⪯_Ψ` is `⊇`, and `(P(Z, Ψ), ⊇)` is a
complete lattice with `inf 𝒜 = cl_Ψ ⋃_{A ∈ 𝒜} A` and `sup 𝒜 = ⋂_{A ∈ 𝒜} A`. -/
theorem proposition_2_3 {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) :
    (∀ D E : Set Z, IsPsiClosed Ψ D → IsPsiClosed Ψ E → (SetLE Ψ D E ↔ E ⊆ D)) ∧
      ∀ 𝒜 : Set (Set Z), (∀ A ∈ 𝒜, IsPsiClosed Ψ A) →
        (IsPsiClosed Ψ (latInf Ψ 𝒜) ∧ (∀ A ∈ 𝒜, A ⊆ latInf Ψ 𝒜) ∧
            ∀ C : Set Z, IsPsiClosed Ψ C → (∀ A ∈ 𝒜, A ⊆ C) → latInf Ψ 𝒜 ⊆ C) ∧
          (IsPsiClosed Ψ (⋂₀ 𝒜) ∧ (∀ A ∈ 𝒜, ⋂₀ 𝒜 ⊆ A) ∧
            ∀ C : Set Z, IsPsiClosed Ψ C → (∀ A ∈ 𝒜, C ⊆ A) → C ⊆ ⋂₀ 𝒜) := by sorry

end SetOptLattice.Existence
