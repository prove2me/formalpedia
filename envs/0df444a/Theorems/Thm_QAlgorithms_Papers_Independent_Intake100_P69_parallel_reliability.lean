-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P69_parallel_reliability
-- name    : QAlgorithms.Papers.Independent.Intake100.P69.parallel_reliability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:27:29.492236+00:00
-- url     : https://prove2.me/theorems/9be01b7f-24e7-41e9-9f25-156083c4b4b4
-- title:
--   Equal-block parallel teleportation is reliable below square-root load
-- statement:
--   Let $(N_j)$ and $(k_j)$ be sequences of positive integers with $N_j\to\infty$, $1\le k_j\le N_j$, and $k_j$ dividing $N_j$. Partition the $N_j$ singlets into $k_j$ equal blocks and run the original deterministic single-qubit port protocol independently on each block, using the square-root effects with a symmetric completion on their common kernel. If $F_{\rm one}(m)$ denotes this physical single-block channel's entanglement fidelity, the joint channel has fidelity $F_{\rm par}(N_j,k_j)=F_{\rm one}(N_j/k_j)^{k_j}$.
--
--   If the input count is sub-square-root, then
--
--   $$
--   \frac{k_j^2}{N_j}\longrightarrow0
--   \quad\Longrightarrow\quad
--   F_{\rm par}(N_j,k_j)\longrightarrow1.
--   $$
--
--   This is the achievable reliability meaning of (9) on exactly the integer resource sizes supporting the source's equal partition. It does not assert the finite physical-fidelity equality printed in (8).
-- source:
--   Generalized teleportation and entanglement recycling, arXiv:1209.2683v2, PDF p. 4, Unnumbered parallel reliability consequence, eq. (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P69

namespace QAlgorithms.Papers.Independent.Intake100.P69

open scoped ComplexConjugate

open Filter

/-- PDF p.4, (7)-(9): on admissible equal-block resource sizes, every
sub-square-root input sequence is reliably teleported by independent original
PBT channels. No exact finite equality from (8) is asserted. -/
theorem parallel_reliability (N k : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hadmissible : ∀ j, 1 ≤ k j ∧ k j ≤ N j ∧ k j ∣ N j)
    (hsmall : Tendsto (fun j => (k j : ℝ) ^ 2 / (N j : ℝ)) atTop (nhds 0)) :
    Tendsto (fun j => singlePortFidelity (N j / k j) ^ k j) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P69
