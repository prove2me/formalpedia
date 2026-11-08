-- Prove2me | Theorems.Thm_RankRobustAssort_proposition_EC_1
-- name    : RankRobustAssort.proposition_EC_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:29:52.639346+00:00
-- url     : https://prove2.me/theorems/c375898b-61d0-4029-bda4-9e235c90f215
-- title:
--   Proposition EC.1 — $\rho_{i_1\cdots i_M}(S)=\min_{i\in S\cap\mathcal I_{i_1\cdots i_M}(S)} r_i$
-- statement:
--   For all $S\in\mathcal S$ and $(i_1,\dots,i_M)\in\mathcal L$,
--
--   $$
--   \rho_{i_1\cdots i_M}(S)=\min_{i\in S\cap\mathcal I_{i_1\cdots i_M}(S)} r_i.
--   $$
--
--   This is the graphical description of the coefficients of (2): the candidates for the top product of $S$ are the products of $S$ with no path to a vertex $i_m$ lying in $S$.
--
--   Differences from the source:
--   - encoding: minima of revenues over finite index sets → minima in $\mathbb R\cup\{+\infty\}$; reason: the index sets are nonempty for $S\in\mathcal S$ and tuples in $\mathcal L$, so the values are the paper's real minima
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition EC.1, p.ec16

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_rho
import Definitions.Def_RankRobustAssort_Ical

open Classical

namespace RankRobustAssort

/-- **Proposition EC.1.** For all `S ∈ 𝒮` and `(i₁,…,i_M) ∈ ℒ`,
`ρ_{i₁⋯i_M}(S) = min_{i ∈ S ∩ ℐ_{i₁⋯i_M}(S)} r_i`.

Sturt, arXiv:2112.05010v4, Proposition EC.1, p.ec16.

Formalization Note: both minima are `Finset.inf` in `WithTop ℝ` (see `rho`); for `S ∋ 0` and a
tuple in `ℒ` both index sets are nonempty, so both sides are the paper's real minima. -/
theorem proposition_EC_1 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (t : Fin M → Fin (n + 1)) (ht : InL P t) :
    rho P t S = (S.filter (fun i => Ical P t S i)).inf (fun i => ((P.r i : ℝ) : WithTop ℝ)) := by sorry

end RankRobustAssort
