-- Prove2me | Theorems.Thm_RegretBandits_Linear_legendre_duality
-- name    : RegretBandits.Linear.legendre_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:14:43.949308+00:00
-- url     : https://prove2.me/theorems/6da25d0a-2963-47db-84af-2bc2c5281c54
-- title:
--   Lemma 5.1 — duality of a Legendre function and its conjugate
-- statement:
--   Let $D\subset\mathbb R^d$ be a nonempty open convex set and let $F$ be a Legendre function on $\bar D$, with Legendre–Fenchel transform $F^*(u)=\sup_{x\in\bar D}(x^\top u-F(x))$ and dual space $D^*=\nabla F(D)$. Then:
--
--   1. $F^{**}=F$ on $\bar D$;
--   2. $\nabla F^*$ is the inverse of $\nabla F$ on $D^*$: $\nabla F^*(\nabla F(x))=x$ for every $x\in D$;
--   3. for all $x,y\in D$,
--   $$D_F(x,y)=D_{F^*}\bigl(\nabla F(y),\nabla F(x)\bigr). \tag{5.2}$$
--
--   The lemma lets the OMD update be read in the dual space. A gradient step on $\nabla F(x_t)$ is mapped back to the primal by $\nabla F^*$, and Bregman divergences in the primal equal Bregman divergences of $F^*$ in the dual. It is the step that rewrites the OMD regret bound in terms of $D_{F^*}$.
--
--   **Formalization Note** $F^{**}$ and $F^*$ are computed in the extended reals. $\nabla F^*$ and $D_{F^*}$ use the real-valued conjugate, which equals $F^*$ on the open set $D^*$. The book refers to Cesa-Bianchi and Lugosi (2006, Proposition 11.1) for the proof.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 70, Lemma 5.1, Eq. (5.2)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics

namespace RegretBandits.Linear

/-- Lemma 5.1 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 70). Let `F` be Legendre on `D̄`.
Then `F** = F` on `D̄`, `∇F*` inverts `∇F` on `D* = ∇F(D)` (`∇F*(∇F(x)) = x` for `x ∈ D`), and
for all `x, y ∈ D`, `D_F(x, y) = D_{F*}(∇F(y), ∇F(x))` (Eq. (5.2)). -/
theorem legendre_duality {d : ℕ} {F : (Fin d → ℝ) → ℝ} {D : Set (Fin d → ℝ)}
    (hF : IsLegendre F D) :
    (∀ x ∈ closure D, legendreBiconj F D x = ((F x : ℝ) : EReal)) ∧
    (∀ x ∈ D, grad (conjReal F D) (grad F x) = x) ∧
    (∀ x ∈ D, ∀ y ∈ D, bregman F x y = dualBregman F D (grad F y) (grad F x)) := by sorry

end RegretBandits.Linear
