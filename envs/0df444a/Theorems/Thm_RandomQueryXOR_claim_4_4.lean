-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_4
-- name    : RandomQueryXOR.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:09:15.388342+00:00
-- url     : https://prove2.me/theorems/a899853c-c507-4bc8-9c89-ec2025cfc78e
-- title:
--   Claim 4.4 — $\mathrm{IC}_\mu(P)\le TS$
-- statement:
--   Let $P$ be a randomized branching program of length $T$ and width $2^S$ in the gate-keeper model over a finite index set, and $\mu$ any distribution on inputs. Then
--   $$
--   \mathrm{IC}_\mu(P)=\sum_{i\in[T]}\ \sum_{j\le i} I\bigl(P_i\,;\,b_j\ \big|\ P_{j-1},y,L,R_{\rm pub}\bigr)\ \le\ T\,S .
--   $$
--
--   This is the upper half of the argument: an $S$-bit memory can carry at most $S$ bits about the gate bits at each of the $T$ times. Combined with the lower bound on the information cost (Lemmas 4.6 and 4.16) it yields Result 1.
--
--   Differences from the source:
--   - generalization: programs reading inputs in {0,1}^{2n} (index set [2n]) → programs over any finite index set ι; reason: the proof uses only the width; it specializes at ι = Fin (2 * n)
--   - encoding: a randomized branching program: a distribution D^A_n on programs with per-node distributions over outgoing edges → a probability distribution (WildeQIT.FinDist) on deterministic layered programs DetBP (2^S) _ T; reason: a run visits one node per layer, so independent per-node edge choices fold into a distribution on deterministic programs; the paper does the same in π_two step (ii)
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_RandomQueryXOR_infoCost

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Claim 4.4 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.17 = PDF p.19): "For any branching program P of length T and width 2^S, for
any input distribution µ, we have IC_µ(P) ≤ TS."

**Formalization Note** `P` is a randomized program in the gate-keeper model (a distribution `μP` on
deterministic programs with `2^S` states per layer) over any finite index set `ι`; `µ` is any
distribution on inputs. No correctness of `P` is assumed (the proof does not use it). -/
theorem claim_4_4 {ι : Type} [Fintype ι] [DecidableEq ι] {S T : ℕ}
    (μP : FinDist (DetBP (2 ^ S) (GateSample ι) T)) (μ : FinDist (ι → Bool)) :
    infoCost μP μ ≤ (T : ℝ) * S := by sorry

end RandomQueryXOR
