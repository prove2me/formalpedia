-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_2_4
-- name    : SignFreeOracle.Separation.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:05.740566+00:00
-- url     : https://prove2.me/theorems/c91d85c9-ca14-4427-b184-d73c9d66514a
-- title:
--   Lemma 2.4 — Euclidean spectral norm of degenerate graphs
-- statement:
--   For a finite simple $c$-degenerate graph $G$ of maximum degree at most $d$, where $c,d$ are nonnegative integers, the actual adjacency matrix satisfies
--   $$\|A_G\|_{2\to2}\le2\sqrt{cd}.$$
--   The norm uses Euclidean vectors and includes the negative spectrum. Empty vertex sets have operator norm zero; isolated and disconnected graphs remain permitted. This is the operator estimate needed to turn the NO graph's 2-degeneracy into its Perron bound.
--
--   Differences from the source:
--   - generalization: maximum degree exactly d → maximum degree at most d; reason: monotonicity in the degree bound includes the original maximum
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 2.4, p. 7 (PDF p. 7)

import Definitions.Def_SignFreeOracle_Separation_Graph

set_option autoImplicit false

namespace SignFreeOracle.Separation

theorem lemma_2_4 {V : Type} [Fintype V] (G : SimpleGraph V) (c d : ℕ)
    (hc : Degenerate G c) (hd : maxDegree G ≤ d) :
    adjNorm G ≤ 2 * Real.sqrt ((c : ℝ) * d) := by sorry

end SignFreeOracle.Separation
