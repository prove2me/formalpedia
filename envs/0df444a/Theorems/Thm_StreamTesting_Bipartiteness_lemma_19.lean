-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_19
-- name    : StreamTesting.Bipartiteness.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:11.752372+00:00
-- url     : https://prove2.me/theorems/f6729d1e-ec1a-42ee-9d70-2fb7cc00a876
-- title:
--   Lemma 19 — short increasing paths in random order
-- statement:
--   Fix a natural degree bound $d$. Put $L(n)=\lceil4\log n/\log\log n\rceil$ and $b_d(n)=nd^{L(n)}/(L(n)+1)!$. There exist $C>0$ and $N_0\ge16$ such that for every $n\ge N_0$,
--
--   $$0<\log\log n,\qquad L(n)\le C\frac{\log n}{\log\log n},\qquad b_d(n)\longrightarrow0\quad(n\longrightarrow\infty).$$
--
--   For every $n\ge16$ and every simple $n$-vertex graph $G$ of maximum degree at most $d$, a uniform arrival order satisfies
--
--   $$\Pr[G\text{ has no increasing simple path of }L(n)\text{ edges}]\ge1-b_d(n).$$
--
--   This gives probability $1-o(1)$ uniformly over the source graphs $G_s$ and over each fixed labeling. The cutoff is the explicit witness in Appendix A.1, not a longer logarithmic cutoff.
--
--   Differences from the source:
--   - generalization: G_s from the fixed graph family, no increasing length-L path with probability 1−o(1) → every maximum-degree-d n-vertex graph, with the explicit tail nd^L/(L+1)! tending to zero; reason: the proof on p.41 proves this union bound for every such graph and fixes exactly this L; applying it to each labeled G_s recovers both source distributions
--   - encoding: L = O(log n/log log n) and sufficiently large n → a uniform positive O-constant, eventual threshold N0 ≥ 16, natural logarithms, and Nat ceiling; reason: the threshold avoids all logarithm defaults and only spells out the source asymptotic regime
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 19, printed p.24 / PDF p.24; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_IncreasingPaths
import Definitions.Def_StreamTesting_Bipartiteness_Neighborhood
import Definitions.Def_PunctSketch_coinProb

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 19, p.24 and its explicit witness and bound, p.41.
The estimate is uniform over every maximum-degree-d graph and every labeling. -/
theorem lemma_19 (d : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ n ≥ N₀,
      0 < Real.log (Real.log (n : ℝ)) ∧
      (cutoff n : ℝ) ≤ C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) ∧
    Filter.Tendsto (pathFailureBound d) Filter.atTop (nhds 0) ∧
    (∀ n : ℕ, 16 ≤ n → ∀ G : SimpleGraph (Fin n), GreedyColoringLCA969.LowerBound.MaxDegreeAtMost G d →
      1 - pathFailureBound d n ≤
        PunctSketch.coinProb (fun σ : Order n => NoIncreasingPath G σ (cutoff n))) := by sorry

end StreamTesting.Bipartiteness
