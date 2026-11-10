-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_theorem_3_1
-- name    : QuantumBipartiteTesting.Bipartiteness.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:13.197994+00:00
-- url     : https://prove2.me/theorems/5851bd1b-b326-49f9-ba2f-9eb13b4c42c2
-- title:
--   Theorem 3.1 — quantum bipartiteness testing lower bound
-- statement:
--   For each fixed degree bound $d\ge3$, there is $\varepsilon_0(d)\in(0,1)$ such that, for every fixed $0<\varepsilon\le\varepsilon_0(d)$, positive constants $c(\varepsilon,d)$ and $N_0(\varepsilon,d)\ge2$ exist with the following property. Every quantum tester on $N\ge N_0$ vertices that accepts every bipartite simple graph and rejects every graph at edge-edit distance at least $\varepsilon Nd$ from bipartiteness, with success probability at least $2/3$ on each promise class, uses
--   $$q\ge c(\varepsilon,d)\frac{N^{1/3}}{\log N}.$$
--   The bound is uniform over all valid neighbor orderings, all finite complex workspaces, all injective binary response encodings, and every sufficiently large integer input size, including sizes not divisible by seven. The distance is minimized over actual target graphs. This is the source's full bipartiteness result, with its small-epsilon standing convention made explicit.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - encoding: fixed d and sufficiently small fixed epsilon under Remark 2.4; Omega(N^(1/3)/log N) → for d>=3 choose epsilon0(d)>0, then c(epsilon,d)>0 and N0(epsilon,d)>=2, uniformly over every N>=N0 and every tester; reason: expands the source standing conventions; natural logarithms change only the positive leading constant; every sufficiently large size is included
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Theorem 3.1, PDF = printed page 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf Repeated with proof on PDF = printed page 21.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness

/-- Remark 2.4 and the fixed-degree convention are quantified explicitly. -/
theorem theorem_3_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k w q : ℕ,
    ∀ E : Encoding (Fin N) k, ∀ A : Algorithm (Address N d) k w q,
    ∀ out : (Address N d × Bits k) × Fin w → Bool,
      BipartiteTester ε E A out → c * LowerBoundScale N ≤ (q : ℝ) := by sorry

end QuantumBipartiteTesting.Bipartiteness
