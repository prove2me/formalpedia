-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_corollary_4_8
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.corollary_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:17:43.145062+00:00
-- url     : https://prove2.me/theorems/ff67e878-0ea7-42ba-848d-b5cf4c741679
-- title:
--   Corollary 4.8 — Both replacement-distribution testing promises
-- statement:
--   There are positive constants $h_0,\alpha$ and an order threshold $c_0$ for which simple cubic clouds with edge expansion $h_0$ exist at every even order $c\ge c_0$. For every fixed $0<\alpha'<\alpha$ and every $\delta>0$, all sufficiently large $n$ satisfy, uniformly for even $c\ge c_0$ with $c\ge400\ln n$ and for every such cloud,
--   $$\Pr_{(M_0,1),\mathrm{feas}}[R_J(H)\text{ is an }\alpha\text{-vertex-expander}]\ge1-\delta,$$
--   $$\Pr_{(M_0,2),\mathrm{feas}}[R_J(H)\text{ is }(\alpha'/12)\text{-far from }\alpha'\text{-vertex-expansion}]=1.$$
--   The same $\alpha$ precedes all $\alpha'$; this records both replacement-distribution promises, with quantitative meaning for $1-o(1)$.
--
--   Differences from the source:
--   - encoding: vertices [n] and asymptotic notation → Fin n, natural logarithms and explicit uniform constants/thresholds; reason: bijective vertex labeling and logarithm-base changes preserve all source instances
--   - generalization: c is an even logarithmic color count with sufficiently large coefficient → all even c at least 400 ln n, without an upper logarithmic bound; reason: the cut-failure sum and replacement promises improve with more independent matching colors; the logarithmic regime is included
--   - encoding: a fixed cubic cloud family and probability 1-o(1) → existence of clouds at every sufficiently large even order, and uniform delta thresholds for every qualifying cloud; reason: the same cloud expansion constant controls all orders; both probability clauses are retained
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Corollary 4.8, printed page = PDF page 25

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem corollary_4_8 :
    ∃ h₀ α : ℝ, 0 < h₀ ∧ 0 < α ∧ ∃ c₀ : ℕ,
      (∀ c ≥ c₀, Even c → ∃ J : Finset (Edge c), Cloud h₀ J) ∧
      ∀ α' : ℝ, 0 < α' → α' < α → ∀ δ : ℝ, 0 < δ →
        ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ c ≥ c₀,
          Even c → 400 * Real.log n ≤ (c : ℝ) →
          ∀ e : Fin (n*c) ≃ Fin n × Fin c, ∀ J : Finset (Edge c), Cloud h₀ J →
            (1 - δ ≤ FeasibleProb n (Center n) 1 c
              (fun H => VertexExpander α (Replacement e J H))) ∧
            FeasibleProb n (Center n) 2 c
              (fun H => ExpansionFar 4 (α'/12) α' (Replacement e J H)) = 1 := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
