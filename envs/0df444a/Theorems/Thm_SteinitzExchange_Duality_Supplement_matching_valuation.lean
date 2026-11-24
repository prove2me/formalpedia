-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_matching_valuation
-- name    : SteinitzExchange.Duality.Supplement.matching_valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:31:21.475682+00:00
-- url     : https://prove2.me/theorems/3743e483-cc4e-4057-808e-a32d58e5d81b
-- title:
--   Theorem 7.3 — a valuated matroid induced through a bipartite matching is a valuated matroid
-- statement:
--   Let $G=(V^+,V^-,A)$ be a finite bipartite graph, $w:A\to\mathbb R$ a weight function, and $\mathbf M^+=(V^+,\mathcal B^+)$ a matroid with valuation $\omega^+:\mathcal B^+\to\mathbb R$. For a matching $M\subseteq A$ let $\partial^+M\subseteq V^+$ and $\partial^-M\subseteq V^-$ be its sets of incident entrance and exit vertices and $w(M)=\sum_{a\in M}w(a)$. Let
--   $$\tilde{\mathcal B}=\{\partial^-M\mid M\ \text{a matching with}\ \partial^+M\in\mathcal B^+\},$$
--   assumed nonempty, and
--   $$\tilde\omega(X)=\max\{w(M)+\omega^+(\partial^+M)\mid M\ \text{matching},\ \partial^+M\in\mathcal B^+,\ \partial^-M=X\}\qquad(X\in\tilde{\mathcal B}).\tag{7.7}$$
--   Then $(V^-,\tilde{\mathcal B})$ is a matroid and $\tilde\omega$ is a valuation of it: for $X,Y\in\tilde{\mathcal B}$ and $u\in X-Y$ there is $v\in Y-X$ with $X-u+v,\ Y+u-v\in\tilde{\mathcal B}$ and $\tilde\omega(X)+\tilde\omega(Y)\le\tilde\omega(X-u+v)+\tilde\omega(Y+u-v)$.
--
--   This is the valuated version of the induction of a matroid through a bipartite graph, and the tool behind the union and truncation theorems (Theorems 7.4 and 7.5).
--
--   **Formalization Note.** `IsValuatedMatroid` is "matroid base family and (MV)". The proviso $\tilde{\mathcal B}\neq\emptyset$ is the paper's ("provided $\tilde{\mathcal B}\neq\emptyset$", p. 305). Parallel arcs between the same two vertices are allowed.
--
--   Differences from the source:
--   - reading: a bipartite graph G = (V⁺, V⁻, A) → finite arc type with endpoint maps src : A → V⁺, dst : A → V⁻; parallel arcs allowed; reason: the page places no simplicity condition on G; parallel arcs are independent arcs of the graph
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 305–306, Theorem 7.3 (Eq. (7.7))

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_Supplement_ValuatedMatroid
import Definitions.Def_SteinitzExchange_Duality_Supplement_MatchingInduction

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 306, Theorem 7.3. Let `G = (V⁺, V⁻, A)` be a bipartite graph, `w : A → ℝ`,
and `M⁺ = (V⁺, ℬ⁺)` a matroid with valuation `ω⁺ : ℬ⁺ → ℝ`. Let
`ℬ̃ = {∂⁻M | M matching, ∂⁺M ∈ ℬ⁺}`, assumed nonempty, and
`ω̃(X) = max{w(M) + ω⁺(∂⁺M) | M matching, ∂⁺M ∈ ℬ⁺, ∂⁻M = X}` (7.7). Then `ω̃` is a valuation
of `(V⁻, ℬ̃)`. -/
theorem matching_valuation {P Q A : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype A]
    (src : A → P) (dst : A → Q) (w : A → ℝ) (ℬp : Finset (Finset P)) (ωp : Finset P → ℝ)
    (hM : IsValuatedMatroid ℬp ωp) (hne : (matchingBase src dst ℬp).Nonempty) :
    IsValuatedMatroid (matchingBase src dst ℬp) (matchingValue src dst w ℬp ωp) := by sorry

end SteinitzExchange.Duality.Supplement
