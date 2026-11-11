-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_15
-- name    : StreamTesting.Bipartiteness.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:21.902211+00:00
-- url     : https://prove2.me/theorems/5ac11dbd-aee8-4741-8769-8b8196df48bc
-- title:
--   Lemma 15 — connected high-girth regular graphs with fixed bipartiteness farness
-- statement:
--   There are a natural degree $d\ge3$ and constants $\gamma,\varepsilon_0>0$ such that, for arbitrarily large positive even sizes $n=2m$, a connected simple $d$-regular graph $H$ on $m$ vertices satisfies
--
--   $$\operatorname{girth}(H)\ge\gamma\log n,\qquad\operatorname{del}_{\mathrm{BIP}}(H)\ge\varepsilon_0dm.$$
--
--   The same three constants serve the entire unbounded family. This supplies both the geometric and farness properties of the base graphs; neither is assumed as an existence premise.
--
--   Differences from the source:
--   - encoding: finite simple graphs on [n], with n/2 base vertices → SimpleGraph (Fin n); base graphs on Fin m and lifts on Fin m × Bool with n = 2m; reason: zero-based relabeling preserves all graphs, unordered edges, arrival permutations, and the exact normalization
--   - encoding: girth inequalities with infinite girth for forests → the same inequality required for every cycle length; reason: cycle-length predicates retain infinite forest girth and do not use the zero-valued natural girth default
--   - encoding: infinitely many sufficiently large n with n/2 base vertices → for every lower threshold N there is m>0 with N ≤ 2m and the stated graph; reason: Appendix A.1 constructs an unbounded family of even witness sizes, so this expresses the full infinite-family conclusion
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 15, printed p.20 / PDF p.20; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Neighborhood
import Definitions.Def_StreamTesting_Bipartiteness_Farness
import Definitions.Def_StreamTesting_Bipartiteness_Girth

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 15, p.20; unbounded even witness sizes n = 2m. -/
theorem lemma_15 :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
    ∀ N : ℕ, ∃ m : ℕ, N ≤ 2 * m ∧ 0 < m ∧
      ∃ H : SimpleGraph (Fin m), H.Connected ∧
        (∀ v, (neighbors H v).card = d) ∧
        GreedyColoringLCA969.LowerBound.GirthAtLeast H (γ * Real.log (2 * (m : ℝ))) ∧ Far H d ε₀ := by sorry

end StreamTesting.Bipartiteness
