-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_11
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:18:50.412881+00:00
-- url     : https://prove2.me/theorems/64c87e03-97b5-47bb-872e-7c2f50274b2c
-- title:
--   Lemma 4.11 — Subdivided NO instances retain distance α′/12
-- statement:
--   Fix any $\alpha'>0$. For all sufficiently large intermediate orders $n$, let $H$ be any graph in the support of the feasible law at $(M_0,2)$ and let $G=R_J(H)$ for any fixed simple cubic cloud with $c>0$ vertices. Put $m=nc$. For every set $T$ of $r\le m/4$ distinct original edges, subdivide each selected edge exactly once, using a separate fresh vertex, to obtain $G'$ on $m+r$ vertices. Then
--   $$\operatorname{dist}_{\alpha'}(G')\ge (\alpha'/12)\,4(m+r).$$
--   The selection can include external edges; the fresh vertex labeling is arbitrary. This retains the exact NO farness with the new vertex-count normalization, permitting arbitrary-size final instances.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - generalization: logarithmically many colors and an expanding fixed cubic cloud → every positive color count and every simple cubic cloud; reason: the separated-block distance argument uses neither cloud expansion nor logarithmic color growth; it includes every source instance
--   - encoding: subdivide r distinct edges once each → a finite selected edge set and arbitrary bijective fresh-vertex labels on Fin (nc+r); reason: no selection is excluded and the distance normalization uses the resulting size
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.11, printed page = PDF page 26; proof p.39

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_11 (α' : ℝ) (hα : 0 < α') :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ c : ℕ, 0 < c →
      ∀ e : Fin (n*c) ≃ Fin n × Fin c, ∀ J : Finset (Edge c), Cubic J →
      ∀ H : Finset (ColoredEdge n c), InSupport n (Center n) 2 c H →
      ∀ T : Finset (Edge (n*c)), T ⊆ Replacement e J H → 4*T.card ≤ n*c →
      ∀ idx : {x // x ∈ T} ≃ Fin T.card,
        ExpansionFar 4 (α'/12) α' (Subdivision (Replacement e J H) T idx) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
