-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_3_3
-- name    : PPRInstOpt.UnknownN.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:43.469335+00:00
-- url     : https://prove2.me/theorems/7d3bfad3-c80c-482c-93c7-b956729512f5
-- title:
--   Lemma 3.3 — Algorithms 6 and 7 with budget κ run in O(κ) time (printed 'Algorithm 4': typo)
-- statement:
--   There is a constant $C>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid graph, for every start vertex and every budget $\kappa\ge 1$, the RAM time of ForwardPushWithFreezing$(s,\kappa)$ (Algorithm 6, with the §3.3 priority-queue implementation) and of BackwardPushWithFreezing$(t,\kappa)$ (Algorithm 7) is at most
--   $$C\,\kappa.$$
--   Lemma 4.4 uses both bounds to charge round $i$ of TriPPR $O(2^i)$ time.
--
--   Differences from the source:
--   - reading: 'The running time of Algorithm 4' → Algorithm 6; reason: typo (finding I3): Algorithm 4 has no budget; the proof is about Algorithm 6
--   - generalization: bound for Algorithm 6 → also the same bound for Algorithm 7; reason: Lemma 4.4 uses it for both algorithms; dropping the second conjunct gives the printed lemma
--   - encoding: O(κf) → ∃ C > 0 depending only on α and εr with time ≤ C κ for all κ ≥ 1; reason: explicit constant
--   - encoding: unit-cost RAM with Θ(log n)-bit words and O(log n)-bit floating point (§1.4, §3.3) → exact real arithmetic; time is the `cost` field, one unit per primitive, with the §3.3 heap bookkeeping charged at its binary-heap cost; reason: reading of §1.4; the floating-point error paragraph of §3.3 is not formalized
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 19, Lemma 3.3

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

namespace PPRInstOpt.UnknownN

/-- Lemma 3.3 (p. 19), read for Algorithm 6 (the printed "Algorithm 4" is a typo), together with
the same bound for Algorithm 7 that Lemma 4.4 uses: there is a constant `C` depending only on `α`
and `εr` such that on every graph, for every start vertex and every budget `κ ≥ 1`, the RAM time of
`ForwardPushWithFreezing(s, κ)` and of `BackwardPushWithFreezing(t, κ)` is at most `C κ`. -/
theorem lemma_3_3 (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr) (hε1 : εr < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V) (κ : ℕ), 1 ≤ κ →
        ((fwdFinal G.oracle α εr κ s).cost : ℝ) ≤ C * κ ∧
        ((bwdFinal G.oracle α εr κ t).cost : ℝ) ≤ C * κ := by sorry

end PPRInstOpt.UnknownN
