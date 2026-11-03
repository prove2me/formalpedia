-- Prove2me | Theorems.Thm_RankRobustAssort_lemma_EC_1
-- name    : RankRobustAssort.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:24.753827+00:00
-- url     : https://prove2.me/theorems/e1d5e236-db0e-431d-a2d0-2ae08c476c42
-- title:
--   Lemma EC.1 — $(i_1,\dots,i_M)\in\mathcal L$ if and only if $\mathcal G_{i_1\cdots i_M}$ is acyclic
-- statement:
--   Let $(i_1,\dots,i_M)\in S_1\times\dots\times S_M$. Then
--
--   $$
--   (i_1,\dots,i_M)\in\mathcal L\iff \mathcal G_{i_1\cdots i_M}\ \text{is acyclic}.
--   $$
--
--   So a choice of one product per past assortment can be realized as the top choices of a single ranking exactly when the "is preferred to" constraints it imposes contain no cycle.
--
--   Differences from the source:
--   - encoding: tuples $(i_1,\dots,i_M)\in S_1\times\dots\times S_M$ (the domain of $\mathcal G$, stated in the proof) → a hypothesis $i_m\in S_m$ for all $m$; reason: the graph is constructed only for such tuples
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.1, p.ec14

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Acyclic

namespace RankRobustAssort

/-- **Lemma EC.1.** For a tuple of products `(i₁,…,i_M) ∈ S₁ × ⋯ × S_M`:
`(i₁,…,i_M) ∈ ℒ` if and only if `𝒢_{i₁⋯i_M}` is acyclic.

Sturt, arXiv:2112.05010v4, Lemma EC.1, p.ec14 (the proof's quantifier: "Consider any tuple of
products (i₁,…,i_M) ∈ S₁ ×···× S_M").

Formalization Note: the tuple is `t : Fin M → Fin (n+1)` with `t m ∈ S m` for all `m`. -/
theorem lemma_EC_1 {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1))
    (ht : ∀ m, t m ∈ P.S m) :
    InL P t ↔ Acyclic P t := by sorry

end RankRobustAssort
