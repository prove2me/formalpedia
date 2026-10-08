-- Prove2me | Theorems.Thm_RegretMatching_Approach_eq_34
-- name    : RegretMatching.Approach.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:12.802428+00:00
-- url     : https://prove2.me/theorems/f4603bb7-0526-4a35-8669-4f6a7c662129
-- title:
--   §3, proof of THEOREM A, p. 1137, (3.4a)–(3.4b) — the left side of (3.3) equals Σ_j α(j)uⁱ(j, s⁻ⁱ)
-- statement:
--   Fix a player $i$, a vector $q$ on $S^i$, a vector $\lambda\in\mathbb R^L$ with $L=\{(j,k)\in S^i\times S^i: j\ne k\}$, and a strategy profile $s$ (only $s^{-i}$ matters). Let $\Lambda_\lambda$ be the matrix with entries $\lambda(j,k)$ for $j\ne k$ and $0$ on the diagonal, and set
--   $$\alpha(j):=\sum_{k\in S^i}q(k)\Lambda_\lambda(k,j)-q(j)\sum_{k\in S^i}\Lambda_\lambda(j,k)\qquad(3.4b).$$
--   Then the left-hand side of (3.3) can be written as (3.4a):
--   $$\sum_{(j,k)\in L}\lambda(j,k)\,q(j)\,\big[u^i(k,s^{-i})-u^i(j,s^{-i})\big]=\sum_{j\in S^i}\alpha(j)\,u^i(j,s^{-i}).$$
--
--   This identity reduces Blackwell's condition for the nonpositive orthant to the invariance equations (3.5): if $\alpha\equiv0$ the left side vanishes for every $s^{-i}$.
--
--   **Formalization Note.** It is an algebraic identity: no hypothesis on $q$ or $\lambda$ is needed. $u^i(k,s^{-i})$ is `u i (Function.update s i k)`, so the $i$-th coordinate of `s` is ignored.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1137, proof of THEOREM A, (3.3), (3.4a), (3.4b)

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem eq_34
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (q : S i → ℝ) (lam : OffDiag (S i) → ℝ) (s : ∀ i, S i) :
    ∑ l : OffDiag (S i), lam l * q l.1.1 *
        (u i (Function.update s i l.1.2) - u i (Function.update s i l.1.1)) =
      ∑ j : S i, (∑ k : S i, q k * lamMat lam k j - q j * ∑ k : S i, lamMat lam j k) *
        u i (Function.update s i j) := by sorry

end RegretMatching.Approach
