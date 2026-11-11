-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_4_5
-- name    : PPRInstOpt.UnknownN.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:14:18.877822+00:00
-- url     : https://prove2.me/theorems/52973d8d-f20c-4a29-b8a8-219f620cc2ef
-- title:
--   Lemma 4.5 — 2^{i*} = O(T* log n)
-- statement:
--   There is a constant $C>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid instance with $n$ vertices and $\pi(s,t)>0$
--   $$2^{i^*}\le C\,T^*\log n.$$
--
--   Differences from the source:
--   - encoding: O(T* log n) → ∃ C > 0 depending only on α and εr; natural logarithm of n = |V| (n ≥ 2 on a valid graph); reason: explicit constant; the base only changes C
--   - encoding: T* = max over r ∈ (0, 1] → supremum over (0, 1]; reason: the family is bounded; the max is attained
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 29, Lemma 4.5

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_TriPPR

namespace PPRInstOpt.UnknownN

/-- Lemma 4.5 (p. 29): there is a constant `C` depending only on `α` and `εr` such that on every
valid instance with `n` vertices, `2^{i*} ≤ C T* log n`. -/
theorem lemma_4_5 (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr) (hε1 : εr < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
        (2 : ℝ) ^ istar α εr G s t ≤ C * Tstar α G s t * Real.log (Fintype.card V) := by sorry

end PPRInstOpt.UnknownN
