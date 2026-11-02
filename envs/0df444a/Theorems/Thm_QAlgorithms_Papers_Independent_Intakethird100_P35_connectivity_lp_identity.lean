-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P35_connectivity_lp_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P35.connectivity_lp_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:20:46.609983+00:00
-- url     : https://prove2.me/theorems/cb5a8427-fafb-4264-a7c7-582249ec9738
-- title:
--   Unnumbered Eqs.(29)–(32),(145): Steiner-cut LP identity
-- statement:
--   Let $G'=(V,E')$ be a finite undirected graph with finite nonnegative capacities $c_e$ and a set $S\subseteq V$ of at least two terminals. An $S$-cut separates at least one pair of terminals, and its capacity is the sum of capacities of its crossing edges, each counted once. Let $f_{s\to t}^{\max}(c)$ denote the usual nonnegative oriented-flow LP with net source objective. In the connectivity LP, each unordered pair of terminals has its own full copy of every edge budget and conservation constraints; a common slack is bounded by every pair's net source flow. Then
--
--   $$\min_{A:\,A\text{ separates }S}\sum_{e\in\partial A}c_e
--   =\min_{\{s,t\}\subseteq S} f_{s\to t}^{\max}(c)
--   =f_S^{\max}(c).$$
--
--   The cut minimum, pair minimum, and connectivity LP maximum are attained. This expresses Steiner connectivity as a linear program of independent pair tests, including disconnected graphs and zero capacities.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, PDF p. 15, Unnumbered Eqs.(29)–(32),(145): Steiner-cut LP identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.15,30, (29)--(32),(145): Steiner cut, smallest pair max-flow,
and the independently budgeted connectivity LP have equal values, with both
extrema attained. S is a set of at least two distinct vertices. -/
theorem connectivity_lp_identity {n e : ℕ} (G : EdgeGraph n (Fin e))
    (hSimple : IsSimple G) (c : Fin e → ℝ) (hc : ∀ a, 0 ≤ c a)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    steinerValue G c S = connectivityValue G c S ∧
    (∃ p : TerminalPair S,
      singlePairFlowValue G c p.val.1 p.val.2 = connectivityValue G c S ∧
      ∀ q : TerminalPair S,
        singlePairFlowValue G c p.val.1 p.val.2 ≤ singlePairFlowValue G c q.val.1 q.val.2) ∧
    (∃ A, SteinerCut S A ∧ cutCapacity G c A = steinerValue G c S ∧
      ∀ B, SteinerCut S B → cutCapacity G c A ≤ cutCapacity G c B) ∧
    (∃ f, ConnectivityFeasible G c S (connectivityValue G c S) f) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P35

end
