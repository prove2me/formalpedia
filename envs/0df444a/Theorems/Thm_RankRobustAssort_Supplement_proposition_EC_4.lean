-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_proposition_EC_4
-- name    : RankRobustAssort.Supplement.proposition_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:39:01.540844+00:00
-- url     : https://prove2.me/theorems/23c8a4f5-ba44-4894-95f1-f7225d35ebf9
-- title:
--   Proposition EC.4 — $\xi_{i_1\cdots i_M}(S)$ is the largest revenue over $S\cap\mathcal I_{i_1\cdots i_M}(S)$
-- statement:
--   For all $S\in\mathcal S$ and $(i_1,\dots,i_M)\in\mathcal L$,
--
--   $$
--   \xi_{i_1\cdots i_M}(S)=\max_{i\in S\cap\mathcal I_{i_1\cdots i_M}(S)} r_i ,
--   $$
--
--   where $\mathcal I_{i_1\cdots i_M}(S)=\{i\in\mathcal N_0:\ i_m\not\prec_{i_1\cdots i_M} i\text{ for every } m \text{ with } i_m\in S\}$ is the set of vertices of the graph $\mathcal G_{i_1\cdots i_M}$ from which no vertex $i_m\in S$ is reachable. This is the graphical description of $\xi$, the counterpart of Proposition EC.1 for $\rho$.
--
--   **Formalization Note.** Both maxima are taken in $\mathbb R\cup\{-\infty\}$; both index sets are nonempty here.
--
--   Differences from the source:
--   - encoding: maxima of revenues over finite index sets → maxima in $\mathbb R\cup\{-\infty\}$; reason: the index sets are nonempty for $S\in\mathcal S$ and tuples in $\mathcal L$, so the values are the paper's real maxima
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only the revenues, the past assortments, rankings, tuples and $\mathcal L$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition EC.4, p.ec54; Definition EC.2, p.ec16

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Ical
import Definitions.Def_RankRobustAssort_Supplement_xi

open Classical

namespace RankRobustAssort.Supplement

/-- **Proposition EC.4.** For all `S ∈ 𝒮` and `(i₁,…,i_M) ∈ ℒ`,
`ξ_{i₁⋯i_M}(S) = max_{i ∈ S ∩ ℐ_{i₁⋯i_M}(S)} r_i`.

Sturt, arXiv:2112.05010v4, Proposition EC.4, p.ec54; `ℐ`, Definition EC.2, p.ec16.

Formalization Note: both maxima are `Finset.sup` in `WithBot ℝ` (see `xi`); for `S ∋ 0` and a
tuple in `ℒ` both index sets are nonempty, so both sides are the paper's real maxima. `ℐ` is the
published `Ical`. -/
theorem proposition_EC_4 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (t : Fin M → Fin (n + 1)) (ht : InL P t) :
    xi P t S =
      (S.filter (fun i => Ical P t S i)).sup (fun i => ((P.r i : ℝ) : WithBot ℝ)) := by sorry

end RankRobustAssort.Supplement
