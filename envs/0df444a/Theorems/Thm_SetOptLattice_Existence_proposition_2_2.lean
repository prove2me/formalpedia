-- Prove2me | Theorems.Thm_SetOptLattice_Existence_proposition_2_2
-- name    : SetOptLattice.Existence.proposition_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:38.823503+00:00
-- url     : https://prove2.me/theorems/e9c97607-4f98-4cb7-9dc6-aec75f85dd5e
-- title:
--   Proposition 2.2, p. 4 — D ↦ cl_Ψ D is a hull operator: extensive, monotone, idempotent
-- statement:
--   Let $(Z,\preceq)$ be a preordered set and $\Psi$ a family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$, with inf-extensions $\psi^\triangle(D)=\inf_{z\in D}\psi(z)$ and hull $\operatorname{cl}_\Psi D=\bigcap_{\psi\in\Psi}\{z\in Z\mid\psi^\triangle(D)\le\psi(z)\}$. Then $D\mapsto\operatorname{cl}_\Psi D$ is a hull operator on the power set of $Z$: for all $D,E\subseteq Z$,
--
--   $$\text{(i) } D\subseteq\operatorname{cl}_\Psi D,\qquad\text{(ii) } D\subseteq E\Rightarrow\operatorname{cl}_\Psi D\subseteq\operatorname{cl}_\Psi E,\qquad\text{(iii) } \operatorname{cl}_\Psi D=\operatorname{cl}_\Psi(\operatorname{cl}_\Psi D).$$
--
--   By (iii) every hull is Ψ-closed, so the family $\mathcal P(Z,\Psi)$ of Ψ-closed sets, the image space of the set optimization problems of the paper, is exactly the range of $\operatorname{cl}_\Psi$.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 4, Proposition 2.2

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Proposition 2.2, p. 4: `D ↦ cl_Ψ D` is a hull operator. -/
theorem proposition_2_2 {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) :
    (∀ D : Set Z, D ⊆ clPsi Ψ D) ∧
      (∀ D E : Set Z, D ⊆ E → clPsi Ψ D ⊆ clPsi Ψ E) ∧
      ∀ D : Set Z, clPsi Ψ D = clPsi Ψ (clPsi Ψ D) := by sorry

end SetOptLattice.Existence
