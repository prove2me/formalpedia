-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_11
-- name    : TwoChoicesSuffice.KOut.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:09.953597+00:00
-- url     : https://prove2.me/theorems/40eac888-e074-47bc-9383-e60127b64360
-- title:
--   Lemma 11 — refined switching inequality for $k\ge3$
-- statement:
--   Let $G$ be a finite simple graph and $k\ge3$ an integer. Couple the random $k$-out subgraph $H^k=H^k_G$ and the augmented two-out graph $H^{2+}=H^{2+}_G$ on the same ordered outcome ($H^{2+}$ uses the first three choices of each vertex, leaders by increasing original degree with a fixed tie-break). Then
--   $$
--   (k-2)\,\mathbb E\bigl[x_G(H^k)\bigr]\le 3\,\mathbb E\bigl[\Phi_G(H^{2+})\bigr].
--   $$
--
--   Combined with Lemma 6 this gives Theorem 10.
--
--   **Formalization Note** The factor $k-2$ is a real number, positive for $k\ge3$.
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: order by increasing original degree, ties broken arbitrarily → ties broken by the LinearOrder instance of V, quantified over every such order; reason: this is the source's 'arbitrary fixed tie-breaking order'; every instance of the source is an instance of the Lean statement
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 11, printed p. 12, PDF p. 13

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 11 (PDF p. 13, printed p. 12). For any simple graph `G` and any integer `k ≥ 3`,
`(k - 2) E[x(H^k)] ≤ 3 E[Φ(H^{2+})]`, with `H^k` and `H^{2+}` coupled on the same ordered
`k`-choice outcome (`H^{2+}` uses its first three positions). -/
theorem lemma_11 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (k : ℕ)
    (hk : 3 ≤ k) :
    ((k : ℝ) - 2) * kOutExpect G k (fun σ => (crossingCount G (prefixGraph G σ k) : ℝ)) ≤
      3 * kOutExpect G k (fun σ => (degPotential G (augTwoOut G σ) : ℝ)) := by sorry

end TwoChoicesSuffice.KOut
