-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_theorem_1
-- name    : ReserveLP.ProLPR.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:43.590074+00:00
-- url     : https://prove2.me/theorems/b562c966-492f-4d6b-a579-038db84fbe10
-- title:
--   Theorem 1, p. 6 — Pro-LPR earns at least (1 + 2(√2−1)e^{√2−2})⁻¹ ≈ 0.684 of the optimal eager second-price revenue
-- statement:
--   Let $\{\beta_{a,b}\}_{a\in\mathsf A,b\in\mathsf B}$ be a data-set of nonnegative bids for a finite set of eager second-price auctions, including the two auxiliary zero-bid buyers. Let $c^\star=2(\sqrt2-1)e^{\sqrt2-2}$. Then:
--
--   1. Profile-LP has an optimal solution $(s^\star,q^\star)$.
--   2. For every optimal solution $(s^\star,q^\star)$, the reserve vector $r^{\rm out}$ returned by the Pro-LPR algorithm satisfies, for every reserve vector $r\ge0$,
--
--   $$\mathbb E\big[\mathrm{Rev}(r^{\rm out})\big]\ \ge\ \frac{1}{1+2(\sqrt2-1)e^{\sqrt2-2}}\ \mathrm{Rev}(r).$$
--
--   Pro-LPR draws each buyer's reserve independently from $q^\star_{b,\cdot}$ and keeps the better of this vector and the zero vector. So its expected revenue is at least a $(1+c^\star)^{-1}\approx0.6844$ fraction of $\mathsf{ESP}^\star$, the optimal revenue of personalized eager reserves. This improves the $1/2$ of Roughgarden and Wang (2016).
--
--   **Formalization Note.**
--   1. "The algorithm" is Pro-LPR, and the bound holds for every optimal LP solution a solver might return. Part 1 makes part 2 non-vacuous.
--   2. The expectation is of the per-realization better choice, $\mathbb E[\max(\mathrm{Rev}(r^{\mathcal R}),\mathrm{Rev}(z))]$.
--   3. $\mathsf{ESP}^\star$ is replaced by the bound against every nonnegative reserve vector.
--   4. The exact constant of the abstract is used; it is $\ge0.684$.
--   5. Running time ("polynomial time") is not formalized.
--   6. Valid profiles require $b_1\neq b_2$, as discussed in the model file. Without this requirement the statement is false.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 6, Theorem 1 (constant from the abstract, p. 1; algorithm Pro-LPR, p. 8)

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem theorem_1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B) :
    (∃ s q, LPOptimal D s q) ∧
      ∀ s q, LPOptimal D s q → ∀ r : B → ℝ, (∀ b, 0 ≤ r b) →
        (1 + cStar)⁻¹ * rev D r ≤ expRevOut D q := by sorry

end ReserveLP.ProLPR
