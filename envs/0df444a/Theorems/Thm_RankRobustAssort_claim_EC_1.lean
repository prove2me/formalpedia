-- Prove2me | Theorems.Thm_RankRobustAssort_claim_EC_1
-- name    : RankRobustAssort.claim_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:30:00.988667+00:00
-- url     : https://prove2.me/theorems/2e2b9768-f928-4920-b3cc-8816663a6f02
-- title:
--   Claim EC.1 — the value of $\rho_{i_1\cdots i_M}(S\cup\{i\})$ for $i\notin S$
-- statement:
--   For all $S\in\mathcal S$, $(i_1,\dots,i_M)\in\mathcal L$ and $i\notin S$:
--
--   1. if $i\notin\mathcal I_{i_1\cdots i_M}(S)$, then $\rho_{i_1\cdots i_M}(S\cup\{i\})=\rho_{i_1\cdots i_M}(S)$;
--   2. if $i\in\mathcal I_{i_1\cdots i_M}(S)$, then
--
--   $$
--   \rho_{i_1\cdots i_M}(S\cup\{i\})=\min\Big\{\min_{j\in S\cap\mathcal I_{i_1\cdots i_M}(S)\cap\{j'\in\mathcal N_0:\ i\not\prec_{i_1\cdots i_M} j'\}} r_j,\ r_i\Big\}.
--   $$
--
--   It describes exactly how one coefficient of (2) changes when a product is added to the assortment.
--
--   Differences from the source:
--   - encoding: minima of revenues over finite index sets → minima in $\mathbb R\cup\{+\infty\}$; reason: the index sets are nonempty for $S\in\mathcal S$ and tuples in $\mathcal L$, so the values are the paper's real minima
--   - encoding: one formula with two cases → the conjunction of the two implications; reason: same content
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Claim EC.1, p.ec16

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_rho
import Definitions.Def_RankRobustAssort_Ical

open Classical

namespace RankRobustAssort

/-- **Claim EC.1.** For all `S ∈ 𝒮`, `(i₁,…,i_M) ∈ ℒ`, and `i ∉ S`,
* `ρ_{i₁⋯i_M}(S ∪ {i}) = ρ_{i₁⋯i_M}(S)` if `i ∉ ℐ_{i₁⋯i_M}(S)`, and
* `ρ_{i₁⋯i_M}(S ∪ {i}) = min { min_{j ∈ S ∩ ℐ_{i₁⋯i_M}(S) ∩ {j' ∈ 𝒩₀ : i ⊀ j'}} r_j , r_i }`
  if `i ∈ ℐ_{i₁⋯i_M}(S)`.

Sturt, arXiv:2112.05010v4, Claim EC.1, p.ec16.

Formalization Note: `S ∪ {i}` is `insert i S`; `i ⊀ j'` is `¬ Reach P t i j'` (no path from `j'`
to `i`). Minima are `Finset.inf` in `WithTop ℝ` and the outer `min` is `⊓`; the inner index set is
nonempty in the second case, and in any case `⊤ ⊓ r_i = r_i`. -/
theorem claim_EC_1 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (t : Fin M → Fin (n + 1)) (ht : InL P t) (i : Fin (n + 1)) (hi : i ∉ S) :
    (¬ Ical P t S i → rho P t (insert i S) = rho P t S) ∧
    (Ical P t S i → rho P t (insert i S) =
      (S.filter (fun j => Ical P t S j ∧ ¬ Reach P t i j)).inf
          (fun j => ((P.r j : ℝ) : WithTop ℝ)) ⊓ ((P.r i : ℝ) : WithTop ℝ)) := by sorry

end RankRobustAssort
