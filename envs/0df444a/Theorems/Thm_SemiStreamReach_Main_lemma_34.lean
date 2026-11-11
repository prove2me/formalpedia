-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_34
-- name    : SemiStreamReach.Main.lemma_34
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:28.307438+00:00
-- url     : https://prove2.me/theorems/17eff31f-8298-43e7-93ba-d4f41523b961
-- title:
--   Lemma 34 — stages of trials that shortcut fixed $2h$-hop paths with probability $1/2$ give an $(h,10\varepsilon\log n)$-hopset w.h.p.
-- statement:
--   Let $G$ be a weighted directed graph on $n$ vertices with positive weights, $h\ge1$ an integer and $0<\varepsilon\le 1/(10\ln n)$. Run Algorithm 4: $T=\lceil\log_2 n\rceil$ stages, each with $N=\lceil C_2\log_2 n\rceil$ independent trials on $K_i=G\cup H_i$. Suppose that for every stage $i$ and every history $H_i$ the earlier stages can produce: for every simple path $P$ in $K_i$ from $u$ to $v$ with at most $2h$ edges and $w_{\min}\le w_{K_i}(P)\le 2n\,w_{\max}$, the output $H'$ of a trial of stage $i$ satisfies
--   $$\Pr\Big[\mathrm{dist}^{(h)}_{K_i\cup H'}(u,v)\le(1+3\varepsilon)\,w_{K_i}(P)\Big]\ \ge\ \tfrac12,\tag{14}$$
--   and that the edges of every $H_{i+1}$ are noncontracting in $G$. Then for every $c>0$ there is a constant $C_2$ (independent of $G$, $n$, $h$, $\varepsilon$ and the trials) such that
--   $$\Pr\big[H_{T+1}\text{ is not an }(h,10\,\varepsilon\ln n)\text{-hopset of }G\big]\ \le\ n^{-c}.$$
--
--   This is the boosting argument of Cao, Fineman and Russell, stated for any trial with the guarantee (14); the streaming trial of §7 is plugged into it.
--
--   **Formalization Note.** Trials are discrete distributions `κ i H` (stage $i$, history $H_i=H$); "conditioned on the random choices of the earlier stages" is the requirement at every history in the support of the law of $H_i$.
--
--   Differences from the source:
--   - reading: "with high probability" with "a sufficiently large constant C2" → ∀ c > 0, ∃ C2 > 0, uniform over all graphs and trials: failure probability ≤ n^{−c} for every n; reason: §3 (p. 13) defines w.h.p. as probability at least 1 − n^{−c} for any fixed c > 0; C2 is chosen before the instance
--   - generalization: log n = log₂ n (the paper's base, cf. "2^{−C2 log n} = n^{−C2}" in the proof, p. 37) in ε ≤ 1/(10 log n) and in 10ε log n → the natural logarithm ln n (T = ⌈log₂ n⌉ and the C2 log n trials as printed); reason: ln n < log₂ n, so the Lean range of ε contains the paper's and the accuracy 10ε ln n is smaller, and an (h, 10ε ln n)-hopset is an (h, 10ε log₂ n)-hopset: the statement specializes to the paper's; the proof's estimate (1 + 3ε)^T ≤ 1 + 10ε ln n still holds, as by convexity it reduces to (1 + 0.3/ln n)^{⌈log₂ n⌉} ≤ 2 (at most 1.67 for every n ≥ 2)
--   - generalization: standing assumptions of §3 (p. 13): polynomial aspect ratio, m ≥ n, 1/ε = O(log^{c0} n) → only positive weights, h ≥ 1 and 0 < ε ≤ 1/(10 ln n) are assumed; reason: the proof uses none of them; the Lean statement specializes to the paper's graphs
--   - encoding: abstract trials, run independently, "conditioned on the random choices of the earlier stages", and the hypotheses on H_{i+1} and K_{i+1} → trial laws κ i H : PMF (WGraph V), a function of the stage i and of H_i (a trial runs on K_i = G ∪ H_i, Algorithm 4 line 5); stage laws built by independent draws; (14) and noncontraction required at every history in the support; K_{i+1} = G ⊓ H_{i+1} contains K_i and the outputs with the same or smaller weights by construction; reason: a randomized trial has a discrete output law; Algorithm 4 sets H_{i+1} = H_i ∪ (outputs), so the containment hypothesis holds automatically
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 37 (PDF 39), Lemma 34

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_IteratedHopset

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 34 (Variant of Lemma 16 of [CFR20]), p. 37 (PDF 39). For every `c > 0` there is a
constant `C2 > 0` such that: for every graph `G` on `n` vertices with positive weights, every
`h ≥ 1`, every `0 < ε ≤ 1/(10 log n)` and all trial laws `κ`, run Algorithm 4 with
`T = ⌈log₂ n⌉` stages of `⌈C2 log₂ n⌉` independent trials. If, at every stage `i` and for every
history `H_i` the earlier stages can produce, every simple path `P` in `K_i = G ∪ H_i` from `u` to
`v` with at most `2h` edges and `w_min ≤ w_{K_i}(P) ≤ 2n·w_max` satisfies (14):
`Pr[dist^(h)_{K_i ∪ H′}(u, v) ≤ (1 + 3ε) w_{K_i}(P)] ≥ 1/2` for the output `H′` of a trial, and if
the edges of every `H_{i+1}` are noncontracting in `G`, then `H_{T+1}` fails to be an
`(h, 10ε log n)`-hopset of `G` with probability at most `n^{−c}`. -/
theorem lemma_34 :
    ∀ c : ℝ, 0 < c → ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (h : ℕ) (ε : ℝ)
        (κ : ℕ → WGraph V → PMF (WGraph V)),
        PositiveWeights G → 1 ≤ h → 0 < ε →
        ε ≤ 1 / (10 * Real.log (Fintype.card V : ℝ)) →
        (∀ i : ℕ, 1 ≤ i → i ≤ Nat.clog 2 (Fintype.card V) →
          ∀ H ∈ (histLaw κ ⌈C2 * Real.logb 2 (Fintype.card V : ℝ)⌉₊ i).support,
            Noncontracting G H) →
        (∀ i : ℕ, 1 ≤ i → i ≤ Nat.clog 2 (Fintype.card V) →
          ∀ H ∈ (histLaw κ ⌈C2 * Real.logb 2 (Fintype.card V : ℝ)⌉₊ (i - 1)).support,
          ∀ (u v : V) (P : List V),
            IsWalkFrom u v P → P.Nodup → P.length ≤ 2 * h + 1 →
            edgeMinWeight G ≤ walkWeight (G ⊓ H) P →
            walkWeight (G ⊓ H) P ≤ 2 * (Fintype.card V : ℝ≥0∞) * edgeMaxWeight G →
            (1 / 2 : ℝ≥0∞) ≤ (κ i H).toOuterMeasure
              {H' | distH (G ⊓ H ⊓ H') h u v ≤
                ENNReal.ofReal (1 + 3 * ε) * walkWeight (G ⊓ H) P}) →
        (histLaw κ ⌈C2 * Real.logb 2 (Fintype.card V : ℝ)⌉₊ (Nat.clog 2 (Fintype.card V))).toOuterMeasure
            {H | ¬ IsHopset G H h (10 * ε * Real.log (Fintype.card V : ℝ))} ≤
          ENNReal.ofReal ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end SemiStreamReach.Main
