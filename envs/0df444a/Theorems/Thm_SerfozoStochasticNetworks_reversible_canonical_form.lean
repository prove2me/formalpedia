-- Prove2me | Theorems.Thm_SerfozoStochasticNetworks_reversible_canonical_form
-- name    : SerfozoStochasticNetworks.reversible_canonical_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-19T02:50:13.226+00:00
-- url     : https://prove2.me/theorems/5ab14461-8e99-4c98-a9a2-76cc833d63c4
-- title:
--   (2.2) — the canonical form of reversible transition rates
-- statement:
--   Let $q$ be a non-negative rate function on a state space and let $\pi$ be strictly positive.
--   Then $\pi$ satisfies the detailed balance equations for $q$,
--   $$\pi(x)q(x,y)=\pi(y)q(y,x)\quad\text{for all }x,y,$$
--   **if and only if** there is a non-negative **symmetric** function $\gamma$ with
--   $$q(x,y)=\frac{\gamma(x,y)}{\pi(x)}\quad\text{for all }x,y .$$
--
--   So the rate functions reversible with respect to a given $\pi$ are exactly the symmetric kernels
--   divided by $\pi$. Besides being a test for reversibility, this is a recipe: any positive $\pi$
--   is the invariant measure of the reversible process built from any symmetric $\gamma$ this way.
--
--   **Formalization Note** The book states the form for $x\ne y$; here it is asserted for all pairs,
--   including the diagonal, which costs nothing — the diagonal value of $\gamma$ is determined as
--   $\pi(x)q(x,x)$ and the detailed balance equation at $x=y$ is an identity.
--
--   $\gamma$ is required to be non-negative, which is where non-negativity of $q$ is used; in the
--   forward direction $\gamma(x,y)=\pi(x)q(x,y)$, and symmetry of that is precisely detailed
--   balance.
--
--   The statement is about a **fixed** $\pi$: it characterizes the rate functions reversible with
--   respect to that $\pi$, rather than asserting the existence of some reversible measure.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, p. 45 (PDF p. 58), restating Theorem 1.5 of p. 6 (PDF p. 19): "Recall from Theorem 1.5 that q is reversible if and only if it is of the form q(x, y) = gamma(x, y)/pi(x), x != y in E, (2.2) for some positive function pi on E and some nonnegative function gamma on E x E such that gamma(x, y) = gamma(y, x), x, y in E. In this case, q is reversible with respect to pi." sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem reversible_canonical_form {E : Type*} (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hπ : ∀ x, 0 < π x) :
    DetailedBalance q π ↔ ∃ γ : E → E → ℝ, (∀ x y, 0 ≤ γ x y) ∧ (∀ x y, γ x y = γ y x) ∧
      ∀ x y, q x y = γ x y / π x := by sorry

end SerfozoStochasticNetworks
