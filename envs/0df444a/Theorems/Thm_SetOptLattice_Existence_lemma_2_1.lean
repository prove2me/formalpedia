-- Prove2me | Theorems.Thm_SetOptLattice_Existence_lemma_2_1
-- name    : SetOptLattice.Existence.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:45.103084+00:00
-- url     : https://prove2.me/theorems/838c2e4e-4663-4bee-a523-4774956881d7
-- title:
--   Lemma 2.1, p. 4 — D ⪯_Ψ E ⇔ cl_Ψ D ⊇ cl_Ψ E; equivalence ⇔ equal hulls; ψ△(cl_Ψ D) = ψ△(D)
-- statement:
--   Let $(Z,\preceq)$ be a preordered set and $\Psi$ a family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$. For $D\subseteq Z$ write $\psi^\triangle(D)=\inf_{z\in D}\psi(z)$ (with $\inf\emptyset=+\infty$), $D\preceq_\Psi E$ if $\psi^\triangle(D)\le\psi^\triangle(E)$ for all $\psi\in\Psi$, and $\operatorname{cl}_\Psi D=\bigcap_{\psi\in\Psi}\{z\mid\psi^\triangle(D)\le\psi(z)\}$. Then for all $D,E\subseteq Z$:
--
--   1. $D\preceq_\Psi E$ if and only if $\operatorname{cl}_\Psi D\supseteq\operatorname{cl}_\Psi E$;
--   2. $D\preceq_\Psi E$ and $E\preceq_\Psi D$ if and only if $\operatorname{cl}_\Psi D=\operatorname{cl}_\Psi E$;
--   3. for every $\psi\in\Psi$,
--   $$\psi^\triangle(\operatorname{cl}_\Psi D)=\psi^\triangle(D). \tag{2.4}$$
--
--   The lemma identifies the preorder $\preceq_\Psi$ with reverse inclusion of hulls, which is what makes $(\mathcal P(Z,\Psi),\supseteq)$ the right ordered set for set optimization.
--
--   **Formalization Note** The page states (c) for $\psi$ without a quantifier; it holds for $\psi\in\Psi$ (the proof uses the definition of $\operatorname{cl}_\Psi D$, which involves only members of $\Psi$), and it is stated so.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 4, Lemma 2.1, (2.4)

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Lemma 2.1, p. 4. -/
theorem lemma_2_1 {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (D E : Set Z) :
    (SetLE Ψ D E ↔ clPsi Ψ E ⊆ clPsi Ψ D) ∧
      ((SetLE Ψ D E ∧ SetLE Ψ E D) ↔ clPsi Ψ D = clPsi Ψ E) ∧
      ∀ ψ ∈ Ψ, infExt ψ (clPsi Ψ D) = infExt ψ D := by sorry

end SetOptLattice.Existence
