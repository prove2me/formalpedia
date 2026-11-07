-- Prove2me | Theorems.Thm_QuantumPRC_theorem_8_9
-- name    : QuantumPRC.theorem_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:27.412287+00:00
-- url     : https://prove2.me/theorems/f09218c0-eecb-4bbc-8ef5-2c55ecde9e0f
-- title:
--   Theorem 8.9 — Recover returns $u$ on a $(t,d)$-good graph
-- statement:
--   Let $t,d$ be positive integers and let $G$ be a graph on $[2n]$ that is $(t,d)$-good for $v\in\{0,1\}^{2n}$. Then for every $u\in\{0,1\}^{2n}$ with $\mathrm{wt}(u)\le t$,
--
--   $$
--   \mathsf{Recover}(G,v\oplus Au)=u,
--   $$
--
--   where $\mathsf{Recover}$ is Construction 8.6 run with the parameters $t,d$ (at most $8t$ flips per block, always the smallest eligible index).
--
--   This is the deterministic half of Theorem 7.1: on a good graph the greedy phase decoder recovers the phase error exactly.
--
--   Differences from the source: none.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 8.9, p.57; Constructions 8.5–8.6, p.55

import Mathlib
import Definitions.Def_QuantumPRC_recover

namespace QuantumPRC

/-- **Theorem 8.9** (deterministic full recovery). Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), Theorem 8.9, p.57: "If `G` is `(t, d)`-good for `v`, then for every `u ∈ {0,1}^{2n}` with
`wt(u) ≤ t`, `Recover(G, v ⊕ Au) = u`."

**Formalization Note.** `Recover` is Construction 8.6 with the parameters `t, d` (`recover t d`),
including the `8t` repetition limit and the smallest eligible `j`; `t, d` are positive, as in
Definition 8.3. -/
theorem theorem_8_9 {n t d : ℕ} (ht : 0 < t) (hd : 0 < d) (G : SimpleGraph (Fin (2 * n)))
    [DecidableRel G.Adj] (v : Bits (2 * n)) (hG : IsGood t d v G) (u : Bits (2 * n))
    (hu : wt u ≤ t) :
    recover t d G (xorB v (adjMul G u)) = u := by sorry

end QuantumPRC
