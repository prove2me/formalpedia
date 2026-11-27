-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_proposition_EC_5
-- name    : RankRobustAssort.Supplement.proposition_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:40:08.359529+00:00
-- url     : https://prove2.me/theorems/de5ce461-acc9-4360-bea4-6d4d2c7d7309
-- title:
--   Proposition EC.5 (corrected: $i^*\in S$) — adding a dominated product never increases $\xi$
-- statement:
--   Let $S\in\mathcal S$ and $i\notin S$. If there exists a product $i^*\in S$ with $r_{i^*}>r_i$ and $\mathcal M_{i^*}\subseteq\mathcal M_i$, then
--
--   $$
--   \xi_{i_1\cdots i_M}(S)\ \ge\ \xi_{i_1\cdots i_M}(S\cup\{i\})\qquad\text{for each }(i_1,\dots,i_M)\in\mathcal L .
--   $$
--
--   Here $\mathcal M_i$ is the set of past assortments that offered $i$. Combined with Proposition EC.3, removing such dominated products from an assortment never lowers its best-case revenue, which is how Theorem EC.1 is proved.
--
--   Differences from the source:
--   - correction: "If there exists $i^*\in\mathcal S$" (printed, p.ec54) → $i^*\in S$; reason: $\mathcal S$ is the collection of assortments, so the printed condition is ill-typed; read as "$i^*$ any product" it is false: $n=2$, $r=(0,1,2)$, one past assortment $S_1=\{0\}$ with $v_{1,0}=1$, $S=\{0\}$, $i=1$, $i^*=2\notin S$ ($\mathcal M_2=\mathcal M_1=\emptyset$) satisfy every other hypothesis, yet $\xi_{0}(S)=0<1=\xi_{0}(S\cup\{1\})$ for the tuple $(0)\in\mathcal L$; the proof reads "Suppose that there exists a product $i^*\in S$" and the analogous Proposition 2 has $i^*\in S$
--   - encoding: maxima of revenues over finite index sets → maxima in $\mathbb R\cup\{-\infty\}$; reason: the index sets are nonempty for $S\in\mathcal S$ and tuples in $\mathcal L$, so the values are the paper's real maxima
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only the revenues, the past assortments, rankings, tuples and $\mathcal L$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition EC.5, p.ec54

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Mset
import Definitions.Def_RankRobustAssort_Supplement_xi

namespace RankRobustAssort.Supplement

/-- **Proposition EC.5** (corrected: `i* ∈ S`). Let `S ∈ 𝒮` and `i ∉ S`. If there exists
`i* ∈ S` that satisfies `r_{i*} > r_i` and `ℳ_{i*} ⊆ ℳ_i`, then
`ξ_{i₁⋯i_M}(S) ≥ ξ_{i₁⋯i_M}(S ∪ {i})` for each `(i₁,…,i_M) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Proposition EC.5, p.ec54 (printed "i* ∈ 𝒮"; the proof, p.ec54,
reads "Suppose that there exists a product i* ∈ S", and the analogous Proposition 2, p.16, has
`i* ∈ S`).

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`, `S ∪ {i}` is `insert i S`, `ℳ_i` is the published `Mset`,
and `ξ` takes values in `WithBot ℝ` (finite on `ℒ` for `S ∋ 0`). -/
theorem proposition_EC_5 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (i : Fin (n + 1)) (hi : i ∉ S)
    (hdom : ∃ i' ∈ S, P.r i < P.r i' ∧ Mset P i' ⊆ Mset P i) :
    ∀ t : Fin M → Fin (n + 1), InL P t → xi P t (insert i S) ≤ xi P t S := by sorry

end RankRobustAssort.Supplement
