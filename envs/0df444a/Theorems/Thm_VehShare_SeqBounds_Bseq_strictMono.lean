-- Prove2me | Theorems.Thm_VehShare_SeqBounds_Bseq_strictMono
-- name    : VehShare.SeqBounds.Bseq_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:54:10.384536+00:00
-- url     : https://prove2.me/theorems/5ac3bb06-441d-4d26-8b1f-47dd5ea4b277
-- title:
--   Proof of Theorem 2: $B^K_{i+1}>B^K_i>B^K_0$
-- statement:
--   Let $N\ge1$ and $W>0$, and let $B^j_i$ be the sequence $B^j_0=0$, $B^j_i=j/(N+j-1+W(1-B^{j-1}_{i-1}))$. Then for every $K$:
--
--   1. $B^K_i>B^K_0=0$ for all $i=1,\dots,K$;
--   2. $B^K_{i+1}>B^K_i$ for all $i=1,\dots,K-1$.
--
--   With $W=\Lambda/\mu$ this is the "Moreover" clause of Theorem 2, and with $W=\lambda/\mu$ it is the paper's remark that the same holds for $B^K_i(q^s)$: each further iteration of the recursion gives a strictly better bound.
--
--   Differences from the source:
--   - generalization: B^K_{i+1} > B^K_i (and, by the same argument, B^K_{i+1}(q^s) > B^K_i(q^s)) → Bseq N W K i < Bseq N W K (i+1) for every W > 0, with N ≥ 1; reason: covers both W = Λ/μ and W = λ/μ, which are positive in the paper's setting
--   - encoding: Λ/μ, positive throughout the paper → the hypothesis W > 0; reason: at W = 0 every B^K_i with 1 ≤ i ≤ K equals K/(N + K − 1), so the strict claim needs it; it excludes no instance of the paper
--   - encoding: B^j_0 = 0 for j = 1, …, K → Bseq N W j 0 = 0 for every j (including B^0_0 = 0); reason: the paper's proof uses B^1_1 = 1/(N + Λ/μ), i.e. B^0_0 = 0
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 2, p. 10 (unnumbered)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_Bseq

namespace VehShare.SeqBounds

/-- **`B^K_{i+1} > B^K_i > B^K_0`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 2, p. 10 (unnumbered: "Next, we show `B^K_{i+1} > B^K_i > B^K_0`
for all `i = 1, 2, ···, K − 1`"; "using the same argument, we can get `B^K_{i+1}(q^s) > B^K_i(q^s)`").

Let `N ≥ 1` and `W > 0`. For every `K`:
1. `0 = B^K_0 < B^K_i` for all `1 ≤ i ≤ K`;
2. `B^K_i < B^K_{i+1}` for all `1 ≤ i ≤ K − 1`.

**Formalization Note.** Stated for every positive workload `W`, which covers both the paper's
`B^K_i` (`W = Λ/μ`) and its `B^K_i(q^s)` (`W = λ/μ`) (a generalization). Reading 10: `W > 0` is
needed; at `W = 0` every `B^K_i` with `1 ≤ i ≤ K` equals `K/(N + K − 1)`. -/
theorem Bseq_strictMono (N : ℕ) (hN : 1 ≤ N) (W : ℝ) (hW : 0 < W) (K : ℕ) :
    (∀ i : ℕ, 1 ≤ i → i ≤ K → Bseq N W K 0 < Bseq N W K i) ∧
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ K → Bseq N W K i < Bseq N W K (i + 1) := by sorry

end VehShare.SeqBounds
