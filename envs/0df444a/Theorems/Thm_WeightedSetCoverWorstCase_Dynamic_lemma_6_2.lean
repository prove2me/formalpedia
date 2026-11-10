-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_6_2
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:03.899765+00:00
-- url     : https://prove2.me/theorems/113c30eb-15d3-4f14-8f84-d667a0ef1218
-- title:
--   Lemma 6.2 — Invariant 6.1 (weak or strong stability) bounds the cost of a hierarchical partial covering by $O(\log n)\cdot\mathrm{OPT}(\mathrm{Alive})$
-- statement:
--   For every $\varepsilon>0$ and $\delta>0$ there is a constant $K$ such that, for every instance with $n$ base elements and positive real costs $c$, every type of element versions, every level bound $L$ and every hierarchical partial covering $(U,\ell,\wp\ell,C,\mathrm{cov})$ with at most one alive version of each base element that satisfies Invariant 6.1 with weak $\varepsilon$-stability and $\delta$-tidiness (w.r.t. $c$),
--   $$\sum_{s\in C}c(s)\ \le\ K\,(1+\log\max(1,n))\cdot \mathrm{OPT}(\mathrm{Alive}),$$
--   where $\mathrm{OPT}(\mathrm{Alive})$ is the minimum cost of a subfamily covering the base elements of the alive versions and the sum pays every copy. Since strong stability implies weak stability, this covers both cases of the lemma. The bound is a cost bound only: $C$ need not cover $\mathrm{Alive}$.
--
--   Differences from the source:
--   - generalization: a universe U of elements, C ⊆ S a collection of sets → a universe of element versions with a base map injective on the alive versions, and a multiset of set copies; reason: §6.1 and footnote 6 apply the lemma to versions and multisets; with versions = base elements (base = id) and distinct copies it is the source's statement
--   - encoding: O(log n)-approximation (ε, δ constants) → ∃ K, depending only on ε and δ and chosen before the instance and L, with cost ≤ K (1 + log max(1, n)) · OPT; reason: the additive 1 makes the bound meaningful at n = 1; n is the number of base elements
--   - encoding: ℓ(s) ≤ ⌊log_{1+ε}(|cov(s)|/c_s)⌋ → (1+ε)^{ℓ(s)} c_s ≤ |cov(s)|; reason: equivalent for nonempty coverage; false for empty coverage as with log 0 = −∞
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
--   - generalization: the normalized costs, parameter L and polynomial aspect assumption of §6.1 → arbitrary positive real costs and any natural level bound L, with no aspect hypothesis; reason: Appendix B bounds the dual mass independently of C and L; the normalized instances are included
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 6.2, p. 22 (PDF 25)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_HPC

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_6_2 (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ (inst : Instance) (V : Type) [DecidableEq V] (H : HPC inst V) (L : ℕ),
      H.IsHPC L → Set.InjOn H.base H.alive → H.Inv61Weak inst.c0 L ε δ →
      copiesCost inst H.C ≤ K * (1 + Real.log (max 1 (inst.u : ℝ))) * inst.OPT0 H.aliveBase := by sorry

end WeightedSetCoverWorstCase.Dynamic
