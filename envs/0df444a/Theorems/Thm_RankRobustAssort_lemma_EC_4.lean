-- Prove2me | Theorems.Thm_RankRobustAssort_lemma_EC_4
-- name    : RankRobustAssort.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:54.410336+00:00
-- url     : https://prove2.me/theorems/da589efb-201b-4357-a3ae-9a4232fa041d
-- title:
--   Lemma EC.4 — $i$ can be most preferred in $S$ under a consistent ranking iff no $j\in S$ is reachable from $i$
-- statement:
--   Let $(i_1,\dots,i_M)\in\mathcal L$, $S\in\mathcal S$ and $i\in S$. Then there exists a ranking $\sigma\in\bigcap_{m\in\mathcal M}\mathcal D_{i_m}(S_m)$ with $i=\arg\min_{j\in S}\sigma(j)$ if and only if
--
--   $$
--   j\not\prec_{i_1\cdots i_M} i\quad\text{for all } j\in S.
--   $$
--
--   Equivalently, $\bigcap_{m}\mathcal D_{i_m}(S_m)\cap\mathcal D_i(S)\ne\emptyset$ exactly when the graph has no path from $i$ to a product of $S$; this is what makes $\rho_{i_1\cdots i_M}(S)$ computable from the graph.
--
--   Differences from the source:
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.4, p.ec15

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Reach

namespace RankRobustAssort

/-- **Lemma EC.4.** Let `(i₁,…,i_M) ∈ ℒ`, `S ∈ 𝒮`, and `i ∈ S`. Then there exists a ranking
`σ ∈ ⋂_{m∈ℳ} 𝒟_{i_m}(S_m)` that satisfies `i = arg min_{j∈S} σ(j)` if and only if
`j ⊀_{i₁⋯i_M} i` for all `j ∈ S`.

Sturt, arXiv:2112.05010v4, Lemma EC.4, p.ec15.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`; `i = arg min_{j∈S} σ(j)` is `IsTop σ S i`. The quantifier
"for all `j ∈ S`" includes `j = i`, as on the page. -/
theorem lemma_EC_4 {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (ht : InL P t)
    (S : Finset (Fin (n + 1))) (hS : 0 ∈ S) (i : Fin (n + 1)) (hi : i ∈ S) :
    (∃ σ : Equiv.Perm (Fin (n + 1)), (∀ m, IsTop σ (P.S m) (t m)) ∧ IsTop σ S i) ↔
      ∀ j ∈ S, ¬ Reach P t j i := by sorry

end RankRobustAssort
