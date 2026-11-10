-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_11
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:12:53.195099+00:00
-- url     : https://prove2.me/theorems/81f4b03c-f1a4-4f6c-bd47-790c64355030
-- title:
--   Lemma 3.11 — uniform grid overflow bound
-- statement:
--   There are an absolute constant $c>0$ and a size threshold $N_0$ such that, for every $N\ge N_0$ and every integer pair $(M,\ell)\in\mathcal G_N$, the sampling parameters are valid and
--   $$\Pr[\text{some block overflows}]\le\exp(-cN^{1/3}).$$
--   Overflow is computed from the $N$ independent uniform block assignments, with capacity $M/\ell$. The same constant and threshold work simultaneously over the entire grid. This controls the effect of conditioning on successful sampling.
--
--   Differences from the source:
--   - encoding: vertices [N], distinct undirected edges and color-labeled parallel edges → Fin N; oriented unordered pairs; color included in each edge identifier; reason: bijections relabel vertices; differently colored parallel constraints remain distinct
--   - encoding: the grid is eventually contained in the valid sampling domain → validity is explicitly concluded together with the overflow bound; reason: page 17 establishes M>=1.09N for large N, while positivity and divisibility are grid conditions; no extra validity hypothesis is added
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.11, PDF = printed page 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_11 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ M l : ℕ, Grid N M l →
      ValidParameters N M l ∧ OverflowProbability N M l ≤ Real.exp (-c * (N : ℝ) ^ (1/3 : ℝ)) := by sorry

end QuantumBipartiteTesting.Bipartiteness
