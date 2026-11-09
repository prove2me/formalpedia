-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_balance_wildcards
-- name    : SubsetSumPartialMatch.SubsetSum.balance_wildcards
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:25.604191+00:00
-- url     : https://prove2.me/theorems/a303ffa2-03a2-435e-806f-bde123751432
-- title:
--   Lemma 3.1 — balancing wildcard positions
-- statement:
--   Let $k,n\ge2$ be even and put $d=\lceil n/k\rceil$. If $E$ is an EXACT$_\mathbb Z$ circuit computing $(P_{k,1/2})^{\otimes d}$, then there is an EXACT$_\mathbb Z$ circuit $C_n$ computing $P_{n,1/2}$ with
--   $$\deg_L(C_n)\le\binom{kd}{d}\deg_L(E),\qquad\deg_R(C_n)\le\deg_R(E).$$
--
--   The lemma reduces arbitrary queries to queries whose wildcards are spread evenly over blocks, at a price paid only on the left degree.
--
--   Differences from the source: none.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 16, Lemma 3.1

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 3.1. Let `k, n ≥ 2` be even and `d = ⌈n/k⌉`. An EXACT_Z circuit `E` for
`(P_{k,1/2})^{⊗d}` gives an EXACT_Z circuit `C_n` for `P_{n,1/2}` with
`deg_L(C_n) ≤ binom(kd, d) deg_L(E)` and `deg_R(C_n) ≤ deg_R(E)`. -/
theorem balance_wildcards {k n d : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (hke : Even k) (hne : Even n)
    (hd : d = ⌈(n : ℝ) / k⌉₊)
    (E : LinCircuit (Fin d → BinStr k) (Fin d → PMCol k (1 / 2)))
    (hE : E.Computes (tensorPow (pm k (1 / 2)) d)) :
    ∃ C : LinCircuit (BinStr n) (PMCol n (1 / 2)), C.Computes (pm n (1 / 2)) ∧
      C.degL ≤ (k * d).choose d * E.degL ∧ C.degR ≤ E.degR := by sorry

end SubsetSumPartialMatch.SubsetSum
