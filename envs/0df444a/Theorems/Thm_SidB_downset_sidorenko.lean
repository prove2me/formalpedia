-- Prove2me | Theorems.Thm_SidB_downset_sidorenko
-- name    : SidB.downset_sidorenko
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T21:27:48.140224+00:00
-- url     : https://prove2.me/theorems/452fd3e2-348d-4788-b378-fb4af1944304
-- title:
--   The weighted Sidorenko theorem for downset graphs (Theorem 3.1)
-- statement:
--   Theorem 3.1 of the paper, the main theorem of Section 3: the weighted Sidorenko theorem for downset graphs. Let r be positive with r at most m, and let alpha be a symmetric integer weight vector such that C(m-k, r-k) divides alpha_k for each 1 <= k <= r and alpha_r is positive. Then for every graphon W, the alpha-weighted homomorphism density of the (m,r)-downset graph is at least the edge density to the power e_alpha(H), the weighted edge count: t_H^alpha(W) >= t_{K_2}(W) ^ e_alpha(H). The proof chains the three lemmas of the section: the weighted downset density is the chain hypergraph density (Lemma 3.2), which is at least the core density to the power C(m,r) (Lemma 3.3), which is at least the edge density to the power e_alpha(H) (Lemma 3.4). The reading as Sidorenko for blow-ups of the downset graph - the vertices of each degree blown up by different amounts - is the interpretation carried in the mission description.
--
--   **Formalization Note** The divisibility hypothesis and the positivity of alpha_r are exactly the hypotheses of the paper; the integer weights enter the weighted density through the cast of the alpha vector into the reals.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 3 (Theorem 3.1, pages 5 and 8).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 6 (Theorem 3.1): the weighted Sidorenko theorem for the
downset graph. Let r be positive with r at most m, and let alpha be a
symmetric integer weight vector such that C(m-k, r-k) divides alpha_k for
each k and alpha_r is positive. Then for every graphon the alpha-weighted
homomorphism density of the (m,r)-downset graph is at least the edge
density to the power e_alpha(H), the weighted edge count. The proof chains
the three lemmas of Section 3: the weighted downset density is the chain
hypergraph density (milestone 3), which is at least the core-chain density
to the power C(m,r) (milestone 4), which is at least the edge density to
the power e_alpha(H) (milestone 5). -/
theorem downset_sidorenko (g : Graphon) (m r : ℕ) (α : ℕ → ℕ) (hr : 0 < r) (hmr : r ≤ m)
    (hdiv : ∀ k, 1 ≤ k → k ≤ r → (m - k).choose (r - k) ∣ α k) (hpos : 0 < α r) :
    g.edgeDens ^ (weightedEdgeCount m r α) ≤ g.downsetDens m r (fun k => (α k : ℝ)) := by sorry

end SidB
