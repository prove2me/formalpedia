-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_4
-- name    : PlantedSubgraphLD.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:07.055085+00:00
-- url     : https://prove2.me/theorems/7ae7b070-df12-4897-af2d-5dcf02ba8d7d
-- title:
--   Lemma 4.4 — treewidth at most $k$ implies $(\ell,3,k+1)$-divisibility
-- statement:
--   Let $k,\ell$ be positive integers. Every finite graph $\Gamma$ with $\mathrm{tw}(\Gamma)\le k$ is $(\ell,3,k+1)$-divisible: every connected graph $F$ with $N_\Gamma(F)>0$ and $e(F)\ge\ell$ has an ordered edge decomposition $(T_1,\dots,T_m)$ with
--
--   $$
--   \ell\le e(T_i)\le3\ell\quad(i=1,\dots,m),\qquad \mathrm{ov}(F,\mathcal T(F))\le(k+1)(m-1).
--   $$
--
--   This is the only use of the treewidth hypothesis (1.2) in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: tw(Γ), the minimum width of a tree decomposition → tw Γ := sInf {w | TreewidthLE Γ w} with the published RobertsonSeymour1986.GM5.TreewidthLE; reason: for a finite graph the set is nonempty and the infimum is attained; same value
--   - encoding: for every connected abstract graph F with NΓ(F) > 0 and e(F) ≥ ℓ, an ordered edge decomposition of F → for every edge set S ⊆ E(Γ) spanning a connected graph with |S| ≥ ℓ, an ordered edge decomposition of S (IsDivisible); reason: decompositions transport along isomorphisms (p.18) with the same piece sizes and overlap, so the abstract and the concrete forms are equivalent
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.4, §4.1, p.20 (PDF p.22); divisibility, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_IsDivisible
import Definitions.Def_PlantedSubgraphLD_tw

namespace PlantedSubgraphLD

/-- **Lemma 4.4.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, Lemma 4.4, p.20 (PDF p.22): "Let k, ℓ be positive integers.
Every graph Γ with treewidth at most k is (ℓ, 3, k + 1)-divisible."

**Formalization Note** Γ is a finite simple graph (§3.1: all graphs are finite). Divisibility is
`IsDivisible`, stated on the concrete copies (see its note). -/
theorem lemma_4_4 (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) (hΓ : tw Γ ≤ k) : IsDivisible Γ ℓ 3 (k + 1) := by sorry

end PlantedSubgraphLD
