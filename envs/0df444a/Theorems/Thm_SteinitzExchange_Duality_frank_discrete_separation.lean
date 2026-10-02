-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_frank_discrete_separation
-- name    : SteinitzExchange.Duality.frank_discrete_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:58:33.916229+00:00
-- url     : https://prove2.me/theorems/f6a72521-28fb-44ad-8ba3-a458fc272560
-- title:
--   Theorem 6.5 — Frank's discrete separation theorem for a submodular/supermodular pair
-- statement:
--   Let $f:2^V\to\mathbb R$ be submodular and $g:2^V\to\mathbb R$ supermodular with $f(\emptyset)=g(\emptyset)=0$. If $g(X)\le f(X)$ for all $X\subseteq V$, then there exists $x^*\in\mathbb R^V$ such that
--
--   $$g(X)\le x^*(X)\le f(X)\qquad(X\subseteq V).$$
--
--   Moreover, if $f$ and $g$ are integer-valued, there exists such an $x^*$ in $\mathbb Z^V$.
--
--   This is Frank's discrete separation theorem (1982), stated in the paper with a citation and no proof. In the duality theorem it yields a common point of $B_1$ and $B_2$ whenever the dual problem is bounded.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 296, Theorem 6.5 (citing [14] = A. Frank, An algorithm for submodular functions on graphs, Ann. Discrete Math. 16 (1982) 97-120)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 296, Theorem 6.5 (Frank's discrete separation theorem [14]). Let
`f : 2^V → ℝ` be submodular and `g : 2^V → ℝ` supermodular with `f(∅) = g(∅) = 0`. If
`g(X) ≤ f(X)` for all `X ⊆ V`, there is `x* ∈ ℝ^V` with `g(X) ≤ x*(X) ≤ f(X)` for all `X ⊆ V`
(Eq. (6.6)). Moreover, if `f` and `g` are integer-valued, such an `x*` exists in `ℤ^V`. -/
theorem frank_discrete_separation {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f g : Finset V → ℝ) (hf : IsSubmodular f) (hg : IsSupermodular g)
    (hf0 : f ∅ = 0) (hg0 : g ∅ = 0) (hgf : ∀ X : Finset V, g X ≤ f X) :
    (∃ xs : V → ℝ, ∀ X : Finset V, g X ≤ ∑ v ∈ X, xs v ∧ ∑ v ∈ X, xs v ≤ f X) ∧
    ((∀ X : Finset V, ∃ k : ℤ, f X = k) → (∀ X : Finset V, ∃ k : ℤ, g X = k) →
      ∃ xs : V → ℤ, ∀ X : Finset V,
        g X ≤ ((sumOn xs X : ℤ) : ℝ) ∧ ((sumOn xs X : ℤ) : ℝ) ≤ f X) := by sorry

end SteinitzExchange.Duality
