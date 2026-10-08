-- Prove2me | Theorems.Thm_RegretMatching_Approach_blackwell_condition_negOrthant
-- name    : RegretMatching.Approach.blackwell_condition_negOrthant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:21.35597+00:00
-- url     : https://prove2.me/theorems/73520b53-b3a7-4265-930d-fbccc924ae3e
-- title:
--   §3, proof of THEOREM A, p. 1137 — an invariant q_λ satisfies (3.3) as an equality: λ·v(q_λ, s⁻ⁱ) = 0
-- statement:
--   Fix a player $i$ and let $L=\{(j,k)\in S^i\times S^i: j\ne k\}$. Let $\lambda\in\mathbb R^L_+$ (all coordinates nonnegative), and let $q_\lambda\in\Delta(S^i)$ satisfy (3.5) for the matrix $\Lambda_\lambda$ with entries $\lambda(j,k)$ off the diagonal and $0$ on it:
--   $$\sum_{k\in S^i}q_\lambda(k)\Lambda_\lambda(k,j)=q_\lambda(j)\sum_{k\in S^i}\Lambda_\lambda(j,k)\qquad\text{for every }j .$$
--   Then for every $s^{-i}$ the expected vector payoff $v(q_\lambda,s^{-i})=\sum_{s^i\in S^i}q_\lambda(s^i)v(s^i,s^{-i})$ is orthogonal to $\lambda$:
--   $$\lambda\cdot v(q_\lambda,s^{-i})=0 .$$
--   Here $v(s^i,s^{-i})\in\mathbb R^L$ has $(j,k)$-coordinate $u^i(k,s^{-i})-u^i(j,s^{-i})$ if $s^i=j$ and $0$ otherwise.
--
--   This is inequality (3.3) "as an equality", and hence Blackwell's condition (3.2) for the nonpositive orthant $\mathbb R^L_-$, whose support function is $0$ on $\mathbb R^L_+$.
--
--   **Formalization Note.** The conclusion is stated as the equality the paper asserts, not the weaker $\le 0$. $\mathbb R^L$ is `EuclideanSpace ℝ L` and $\lambda\cdot x$ is its inner product. The profile `s` stands for $s^{-i}$; its $i$-th coordinate is ignored by $v$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1137, proof of THEOREM A, (3.3) and (3.5), footnote 17

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem blackwell_condition_negOrthant
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (lam : EuclideanSpace ℝ (OffDiag (S i))) (hlam : ∀ l, 0 ≤ lam l)
    (q : S i → ℝ) (hq : q ∈ stdSimplex ℝ (S i))
    (h35 : ∀ j : S i, ∑ k : S i, q k * lamMat (fun l => lam l) k j
      = q j * ∑ k : S i, lamMat (fun l => lam l) j k) :
    ∀ s : ∀ i, S i, inner ℝ lam (∑ a : S i, q a • vecPay u i a s) = 0 := by sorry

end RegretMatching.Approach
