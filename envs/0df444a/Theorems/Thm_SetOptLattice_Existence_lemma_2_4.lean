-- Prove2me | Theorems.Thm_SetOptLattice_Existence_lemma_2_4
-- name    : SetOptLattice.Existence.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:42.117498+00:00
-- url     : https://prove2.me/theorems/f71ae1a0-6098-454a-87ef-6497e7b4e9a1
-- title:
--   Lemma 2.4, p. 5 — inf-stability: ψ△(cl_Ψ ⋃_{A∈𝒜} A) = inf_{A∈𝒜} ψ△(A) for 𝒜 ⊆ P(Z,Ψ)
-- statement:
--   Let $(Z,\preceq)$ be a preordered set and $\Psi$ a family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$ with inf-extensions $\psi^\triangle(D)=\inf_{z\in D}\psi(z)$. If $\mathcal A$ is a family of Ψ-closed sets, $\mathcal A\subseteq\mathcal P(Z,\Psi)$, then for every $\psi\in\Psi$
--
--   $$\psi^\triangle\Big(\operatorname{cl}_\Psi\bigcup_{A\in\mathcal A}A\Big)=\inf_{A\in\mathcal A}\psi^\triangle(A). \tag{2.7}$$
--
--   Since the left-hand side is $\psi^\triangle(\inf\mathcal A)$ in the lattice $(\mathcal P(Z,\Psi),\supseteq)$, the lemma says that each inf-extension $\psi^\triangle$ turns lattice infima into scalar infima (inf-stability). This is the bridge between the set-valued problem and its scalarizations used throughout §3 and §4.
--
--   **Formalization Note** For $\mathcal A=\emptyset$ both sides are $+\infty$ (the empty infimum in `EReal` is $\top$).
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 5, Lemma 2.4, (2.7)

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Lemma 2.4, p. 5 (inf-stability, (2.7)). -/
theorem lemma_2_4 {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (𝒜 : Set (Set Z)) (h𝒜 : ∀ A ∈ 𝒜, IsPsiClosed Ψ A) :
    ∀ ψ ∈ Ψ, infExt ψ (latInf Ψ 𝒜) = ⨅ A ∈ 𝒜, infExt ψ A := by sorry

end SetOptLattice.Existence
