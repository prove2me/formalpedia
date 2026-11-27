-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_claim_EC_15
-- name    : RankRobustAssort.Supplement.claim_EC_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:39:33.898794+00:00
-- url     : https://prove2.me/theorems/58c70e14-192a-4cd6-b747-62824e33b53f
-- title:
--   Claim EC.15 — the value of $\xi_{i_1\cdots i_M}(S\cup\{i\})$ for a product $i\notin S$
-- statement:
--   For all $S\in\mathcal S$, $(i_1,\dots,i_M)\in\mathcal L$ and $i\notin S$,
--
--   $$
--   \xi_{i_1\cdots i_M}(S\cup\{i\})=\begin{cases}\xi_{i_1\cdots i_M}(S), & i\notin\mathcal I_{i_1\cdots i_M}(S),\\[4pt] \max\Bigl\{\max_{j\in S\cap\mathcal I_{i_1\cdots i_M}(S)\cap\{j'\in\mathcal N_0:\ i\not\prec_{i_1\cdots i_M}j'\}} r_j,\ r_i\Bigr\}, & i\in\mathcal I_{i_1\cdots i_M}(S),\end{cases}
--   $$
--
--   where $i\not\prec_{i_1\cdots i_M}j'$ means that $i$ is not reachable from $j'$ in the graph $\mathcal G_{i_1\cdots i_M}$ (a path has at least one edge). It is the step used to show that adding a dominated product never increases $\xi$ (Proposition EC.5).
--
--   **Formalization Note.** Maxima are taken in $\mathbb R\cup\{-\infty\}$; if the inner index set is empty, the inner maximum is $-\infty$ and the outer maximum is $r_i$.
--
--   Differences from the source:
--   - encoding: maxima of revenues over finite index sets → maxima in $\mathbb R\cup\{-\infty\}$; reason: $\xi$ is a real maximum for $S\in\mathcal S$ and tuples in $\mathcal L$; for an empty inner index set the outer maximum is $r_i$
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only the revenues, the past assortments, rankings, tuples and $\mathcal L$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Claim EC.15, p.ec54

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Ical
import Definitions.Def_RankRobustAssort_Reach
import Definitions.Def_RankRobustAssort_Supplement_xi

open Classical

namespace RankRobustAssort.Supplement

/-- **Claim EC.15.** For all `S ∈ 𝒮`, `(i₁,…,i_M) ∈ ℒ`, and `i ∉ S`,
* `ξ_{i₁⋯i_M}(S ∪ {i}) = ξ_{i₁⋯i_M}(S)` if `i ∉ ℐ_{i₁⋯i_M}(S)`, and
* `ξ_{i₁⋯i_M}(S ∪ {i}) = max { max_{j ∈ S ∩ ℐ_{i₁⋯i_M}(S) ∩ {j' ∈ 𝒩₀ : i ⊀ j'}} r_j , r_i }`
  if `i ∈ ℐ_{i₁⋯i_M}(S)`.

Sturt, arXiv:2112.05010v4, Claim EC.15, p.ec54.

Formalization Note: `S ∪ {i}` is `insert i S`; `i ⊀ j'` is `¬ Reach P t i j'` (no path of at
least one edge from `j'` to `i`, published `Reach`). Maxima are `Finset.sup` in `WithBot ℝ` and the
outer `max` is `⊔`; if the inner index set is empty its value is `⊥` and `⊥ ⊔ r_i = r_i`. -/
theorem claim_EC_15 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (t : Fin M → Fin (n + 1)) (ht : InL P t) (i : Fin (n + 1)) (hi : i ∉ S) :
    (¬ Ical P t S i → xi P t (insert i S) = xi P t S) ∧
    (Ical P t S i → xi P t (insert i S) =
      (S.filter (fun j => Ical P t S j ∧ ¬ Reach P t i j)).sup
          (fun j => ((P.r j : ℝ) : WithBot ℝ)) ⊔ ((P.r i : ℝ) : WithBot ℝ)) := by sorry

end RankRobustAssort.Supplement
