-- Prove2me | Theorems.Thm_RankRobustAssort_proposition_1
-- name    : RankRobustAssort.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:10.764487+00:00
-- url     : https://prove2.me/theorems/214b96a0-54a4-429a-b579-b61c91948267
-- title:
--   Proposition 1 — $\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$ equals the optimal value of the linear program (2)
-- statement:
--   Consider a problem instance whose consistent set $\mathcal U$ is nonempty. For each assortment $S\in\mathcal S$ (that is, $0\in S$),
--
--   $$
--   \min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)=\text{the optimal objective value of the linear program (2)},
--   $$
--
--   where (2) minimizes $\sum_{(i_1,\dots,i_M)\in\mathcal L}\rho_{i_1\cdots i_M}(S)\lambda_{i_1\cdots i_M}$ over weights $\lambda\ge0$ on the tuples in $\mathcal L$ summing to $1$ and errors $\epsilon$ with $\|\epsilon\|\le\eta$ and $\sum_{(i_1,\dots,i_M)\in\mathcal L: i_m=i}\lambda_{i_1\cdots i_M}-\epsilon_{m,i}=v_{m,i}$ for all $m\in\mathcal M$, $i\in S_m$.
--
--   This turns the worst-case revenue, a minimization over the $(n+1)!$-dimensional set $\mathcal U$, into a linear program whose feasible set does not depend on $S$: comparing two assortments reduces to comparing their coefficients $\rho_{i_1\cdots i_M}$.
--
--   Differences from the source:
--   - encoding: standing assumption $\mathcal U\ne\emptyset$ stated once on p.8 → explicit hypothesis; reason: the paper assumes it throughout; same instances
--   - encoding: $\min_{\lambda\in\mathcal U}\mathcal R^\lambda(S)$ → infimum of $\{\mathcal R^\lambda(S):\lambda\in\mathcal U\}$; reason: with $\mathcal U\ne\emptyset$ the set is nonempty, bounded below by 0 and its infimum is attained
--   - encoding: optimal objective value of (2), variables indexed by $\mathcal L$ → infimum of the objective over feasible points, with weights on all tuples of which only those in $\mathcal L$ are used; reason: the objective is bounded below by 0 and attained when (2) is feasible; entries outside $\mathcal L$ appear nowhere
--   - encoding: real coefficient $\rho_{i_1\cdots i_M}(S)$ → the extended-real $\rho$ read as a real with default 0 at $+\infty$; reason: for $S\in\mathcal S$ and tuples in $\mathcal L$ the coefficient is finite
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition 1, p.15

import Mathlib
import Definitions.Def_RankRobustAssort_worstCase
import Definitions.Def_RankRobustAssort_lpValue

namespace RankRobustAssort

/-- **Proposition 1.** For each `S ∈ 𝒮`, `min_{λ∈𝒰} ℛ^λ(S)` is equal to the optimal objective
value of the linear optimization problem (2).

Sturt, arXiv:2112.05010v4, Proposition 1, p.15.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`. The paper's standing assumption `𝒰 ≠ ∅` (p.8) is the
hypothesis `hU`; under it both sides are attained minima (see `worstCase`, `lpValue`). -/
theorem proposition_1 {n M : ℕ} (P : Problem n M) (hU : (consistentSet P).Nonempty)
    (S : Finset (Fin (n + 1))) (hS : 0 ∈ S) :
    worstCase P S = lpValue P S := by sorry

end RankRobustAssort
