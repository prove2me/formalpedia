-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_topology_pattern_comparison
-- name    : QuantumBipartiteTesting.Bipartiteness.topology_pattern_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:24:01.412882+00:00
-- url     : https://prove2.me/theorems/7ff7055a-ca11-4c69-bedc-cb80e77ab5b7
-- title:
--   Finite comparison of formal topology moments and feasible pattern containment
-- statement:
--   Fix valid parameters $N,M,l$, with $l\ge1$, $N\le M$, and $2l\mid M$. Let $F$ be a consistent colored graph pattern on the $N$ visible vertices, and suppose
--
--   $$
--   2|F|\le M/l.
--   $$
--
--   If $G$ is sampled by the published feasible hidden-block construction, then its containment probability satisfies
--
--   $$
--   \left|\Pr_{\mathrm{feas}}[F\subseteq G]-W_F(M,l)\right|
--   \le\Pr[\mathrm{overflow}],
--   $$
--
--   where $W_F$ is the formal topology functional defined by the partition sums (A.2)–(A.4).
--
--   This comparison identifies the formal functional through the moments of the observed pattern, rather than defining it to be an overflow-completed graph distribution. The capacity hypothesis ensures that the matching moments for every placement of the pattern are finite probabilities. The result supplies the topology component of the response-monomial comparison in Lemma 3.12.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §3.2 Definition 3.7, Appendix A.2 equations (A.2)–(A.4), printed pp.30–31, and Appendix A.4 monomial coupling estimate for Lemma 3.12. The explicit finite capacity condition guarantees that each pattern matching moment is a probability.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.topology_pattern_comparison {N colors : ℕ} (M l : ℕ) (hv : ValidParameters N M l)
    (F : Finset (ColoredEdge N colors)) (hF : Consistent F) (hsmall : 2*F.card ≤ M/l) :
    |FeasibleBase N M l (fun G : Finset (ColoredEdge N colors) => if F ⊆ G then (1:ℝ) else 0)-
      TopologyMoment F M l| ≤ OverflowProbability N M l := by sorry
