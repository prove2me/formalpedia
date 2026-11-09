-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_claim_4_2
-- name    : RecoveryStorage3SUM.Adaptive.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:59.308821+00:00
-- url     : https://prove2.me/theorems/4507b930-8522-4385-896e-03e2faffb44f
-- title:
--   Claim 4.2 — the collision probability of the padded self-map
-- statement:
--   Let $p\ge1$, let $A_i$ be a part of a partition of $A$, and let $G$ be the padded self-map of $[2p]$ for $A_i$. With loads $d_{i,r}=|M_r\cap(A_i\times B)|$,
--   $$q(G)\le\frac1p+\sum_{r\in[p]}\frac{d_{i,r}^2}{4p^2}.$$
--
--   Combined with Lemma 2.3 and the load check, this bounds the total stored size of the inverters.
--
--   Differences from the source:
--   - generalization: the source run with bounded equal-size inputs, a sampled R, a prime in its range and balanced parts → arbitrary finite integer sets A, B and R, any positive modulus p, any L and any labelled partition, with no cardinality, sampling, coverage or load-check assumptions; reason: the dummy-label fibers have at most two points and each domain residue fiber is bounded by the full load, even if a part is oversized; the source construction is an instance
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Claim 4.2, p.10

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction
import Definitions.Def_RecoveryStorage3SUM_Adaptive_OracleMachine

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Claim 4.2, p.10: `q(G_i^{(k)}) ≤ 1/p + ∑_{r∈[p]} d_{i,r}² / (4p²)` for the padded self-map of `[2p]`. -/
theorem claim_4_2 {A : Finset ℤ} {L : ℕ} (B R : Finset ℤ) (p : ℕ) (hp : 0 < p) (π : A → Fin L)
    (i : Fin L) :
    collisionProb (2 * p) (paddedMap (part π i) B R p) ≤
      1 / (p : ℝ) + ∑ r ∈ Finset.range p, ((load B R p π i r : ℝ) ^ 2 / (4 * (p : ℝ) ^ 2)) := by sorry

end RecoveryStorage3SUM.Adaptive
