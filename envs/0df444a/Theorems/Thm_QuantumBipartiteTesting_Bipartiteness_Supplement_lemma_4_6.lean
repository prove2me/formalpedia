-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_6
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:15:34.526405+00:00
-- url     : https://prove2.me/theorems/b83c24b6-6e86-4bd0-b8c8-77f2c568ee3e
-- title:
--   Lemma 4.6 — Replacement NO instances have distance at least α′/12
-- statement:
--   For every fixed $\alpha'>0$, all sufficiently large intermediate orders $n$, every $c>0$, and every fixed simple cubic cloud $J$, every $H$ in the support of the actual feasible law at $(M_0,2)$ satisfies
--   $$\operatorname{dist}_{\alpha'}(R_J(H))\ge (\alpha'/12)\,4nc.$$
--   Consequently, this farness event has probability exactly one. The support and the probability are both computed from the actual sampling data. No upper bound on $\alpha'$ is imposed. This supplies the replacement NO promise.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - generalization: logarithmically many colors and an expanding fixed cubic cloud → every positive color count and every simple cubic cloud; reason: the separated-block distance argument uses neither cloud expansion nor logarithmic color growth; it includes every source instance
--   - encoding: epsilon-far from expansion → an ENNReal infimum over actual simple targets, normalized by 4nc; reason: an empty target class has infinite distance; support-wise farness and probability one are both retained
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.6, printed page = PDF page 24

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_6 (α' : ℝ) (hα : 0 < α') :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ c : ℕ, 0 < c →
      ∀ e : Fin (n*c) ≃ Fin n × Fin c, ∀ J : Finset (Edge c), Cubic J →
        (∀ H : Finset (ColoredEdge n c), InSupport n (Center n) 2 c H →
          ExpansionFar 4 (α'/12) α' (Replacement e J H)) ∧
        FeasibleProb n (Center n) 2 c
          (fun H => ExpansionFar 4 (α'/12) α' (Replacement e J H)) = 1 := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
