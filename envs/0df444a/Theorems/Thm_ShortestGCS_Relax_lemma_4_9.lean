-- Prove2me | Theorems.Thm_ShortestGCS_Relax_lemma_4_9
-- name    : ShortestGCS.Relax.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:08.176929+00:00
-- url     : https://prove2.me/theorems/5f63b5c4-8093-4058-99e0-528fe2b92afe
-- title:
--   Lemma 4.9, p. 6 — the perspective 𝒳̃ and the cone of valid inequalities 𝒳° are dual to each other
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a nonempty closed convex set, $\tilde{\mathcal X}$ its perspective and $\mathcal X^\circ$ its cone of valid inequalities. With the dual cone taken for the pairing $\langle (a, b), (x, \lambda) \rangle = a^\top x + b\lambda$ on $\mathbb R^n \times \mathbb R$,
--
--   $$
--   (\tilde{\mathcal X})^* = \mathcal X^\circ \qquad\text{and}\qquad (\mathcal X^\circ)^* = \tilde{\mathcal X}.
--   $$
--
--   The second identity is the form used later: a point $(x, \lambda)$ lies in the perspective exactly when $a^\top x + b\lambda \ge 0$ for every valid inequality $(a, b)$ of $\mathcal X$. It converts the infinitely many inequalities of the relaxation $\mathcal S'$ into perspective-cone membership.
--
--   **Formalization Note** Nonemptiness of $\mathcal X$ is added: for $\mathcal X = \emptyset$ the perspective is empty while $\mathcal X^\circ = \mathbb R^{n+1}$ has dual $\{0\}$, so the second identity fails. The paper's sets $\mathcal X_v$ are nonempty by the standing assumptions of Section 2. The paper's phrase "closed convex cones" is a presupposition and is not part of the Lean conclusion.
-- source:
--   arXiv:2101.11565v5, Lemma 4.9, p. 6 (proof p. 7)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Lemma 4.9, arXiv:2101.11565v5, p. 6: for a nonempty closed convex set `𝒳 ⊆ ℝⁿ`, the cones `𝒳̃` and `𝒳°`
are dual to each other: `(𝒳̃)* = 𝒳°` and `(𝒳°)* = 𝒳̃`, for the pairing `((a, b), (x, λ)) ↦ aᵀx + bλ`.
Nonemptiness is added: for `𝒳 = ∅`, `𝒳̃ = ∅` while `(𝒳°)* = {0}`. -/
theorem lemma_4_9 {n : ℕ} (X : Set (Fin n → ℝ)) (hXne : X.Nonempty) (hXc : IsClosed X)
    (hXcv : Convex ℝ X) :
    dualCone (ShortestGCS.MICP.perspectiveSet X) = validCone X ∧ dualCone (validCone X) = ShortestGCS.MICP.perspectiveSet X := by sorry

end ShortestGCS.Relax
