-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_everett
-- name    : ServiceParts.StockLevels.everett
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:40:12.116458+00:00
-- url     : https://prove2.me/theorems/ebe8bf63-5331-4cef-bb13-1a94bdb6bc29
-- title:
--   Theorem 10 (Everett) — a minimizer of the Lagrangian solves the problem with budget b′ = g(x⁰(θ))
-- statement:
--   Let $S$ be a set, let $f$ and $g$ be real functions on $S$, and let $b \in \mathbb{R}$. Problem 1 is
--   $$\min\,\{ f(x) : g(x) \le b,\ x \in S \},$$
--   and for a multiplier $\theta \ge 0$ its Lagrangian relaxation, Problem 2, is $\min_{x \in S}\,[\,f(x) + \theta(g(x) - b)\,]$.
--
--   **Theorem (Everett).** Suppose $x^0(\theta) \in S$ is an optimal solution of Problem 2 for the multiplier $\theta \ge 0$, and let $b' = g(x^0(\theta))$. Then $x^0(\theta)$ also solves Problem 3,
--   $$\min\,\{ f(x) : g(x) \le b',\ x \in S \}:$$
--   it is feasible for Problem 3 and $f(x^0(\theta)) \le f(x)$ for every $x \in S$ with $g(x) \le b'$.
--
--   By varying $\theta$ one obtains optimal solutions of the constrained problem for a family of budgets; if $b' = b$ for some $\theta$, Problem 1 itself is solved.
--
--   **Formalization Note** The book assumes $f$ and $g$ convex and $x$ a vector; the statement here drops both assumptions (a labelled generalization: the proof uses neither, and the book applies the theorem to integer stock vectors, where convexity in the vector-space sense is not defined). The conclusion is stated as: $f(x^0)$ is the least value of $f$ on $\{x \in S : g(x) \le b'\}$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 57, Section 3.4.1, Theorem 10, Eqs. (3.37)-(3.39)

import Mathlib

namespace ServiceParts.StockLevels

theorem everett {X : Type*} (S : Set X) (f g : X → ℝ) (b θ : ℝ) (hθ : 0 ≤ θ)
    (x0 : X) (hx0 : x0 ∈ S)
    (hopt : ∀ x ∈ S, f x0 + θ * (g x0 - b) ≤ f x + θ * (g x - b)) :
    IsLeast (f '' {x | x ∈ S ∧ g x ≤ g x0}) (f x0) := by sorry

end ServiceParts.StockLevels
