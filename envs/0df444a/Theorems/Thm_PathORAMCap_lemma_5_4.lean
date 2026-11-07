-- Prove2me | Theorems.Thm_PathORAMCap_lemma_5_4
-- name    : PathORAMCap.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:26.074196+00:00
-- url     : https://prove2.me/theorems/5b0e39be-a774-48b3-8136-3f8e3926c103
-- title:
--   Lemma 5.4 — $\mathbb E[F_v]\ge\mathbb E[\min\{K,Q^{(3)}_H\}]-K2^He^{-T/2^H}-3KTq$
-- statement:
--   Let $N=2^L$ and $\pi=P_{3,N}(N,(1,\dots,N))$ be the full scan, and take integers $H\ge1$, $K\ge1$, $0\le d\le L-H$ and $1\le n\le N$. With $q=2^{-d}$ and $T=nq$, every node $v$ at depth $d$ satisfies
--
--   $$\mathbb E[F_v]\ge\mathbb E\bigl[\min\{K,Q^{(3)}_H\}\bigr]-K2^He^{-T/2^H}-3KTq,$$
--
--   where $F_v=\min\{K,D^{(3)}(A^{\mathrm{disc}}_v)\}$ is the capped local overflow of the region of $v$ (44). The two losses pay for observing the region only for a finite window and for the discrete scan rounds.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: §5's full scan π = P_{3,N}(N, (1, …, N)) with N = 2^L and its reverse blocks i = 1, …, N → the scan α = id : Fin N → Fin N on Labels (2^L) (2^L); reverse block i is the block with Fin value N − i; reason: the same process; address N − i + 1 is Fin value N − i
--   - encoding: Q_h, the root overflow of an independent geometric-load tree of height h (Definition 4.2) → QLaw Z h : PMF ℕ, defined by the law recursion (16)/(48) from Q_0 = 0; reason: the recursion, stated in the paper, determines the law uniquely; every statement involves Q_h only through its law
--   - encoding: 0 ≤ d ≤ L − H → d + H ≤ L (natural numbers); reason: the same condition on integers; it keeps H ≤ L, which truncated subtraction would lose
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 5.4, p.40 (PDF p.43), eq. (49); parameters (43)–(44), p.38 (PDF p.41)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST
import Definitions.Def_PathORAMCap_QLaw
import Definitions.Def_PathORAMCap_regionF

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Lemma 5.4** (Local Comparison with Two Explicit Losses; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.40 (PDF p.43)): "For the full
scan and parameters in (43), every node v at depth d satisfies
E[Fv] ≥ E[min{K, Q(3)H}] − K2^He^(−T/2^H) − 3KTq, q = 2^−d, T = nq. (49)"

**Formalization Note.** §5's setting (p.36): `N = 2^L` and the full scan `P_{3,N}(N, (1, …, N))`.
Parameters (43), p.38: integers `H ≥ 1`, `K ≥ 1`, `0 ≤ d ≤ L − H` (written `d + H ≤ L`, so that
`H ≤ L`), `1 ≤ n ≤ N`. `F_v` is (44) (`regionF`); `E[min{K, Q^(3)_H}]` is finite (at most `K`) and
enters as a real number. -/
theorem lemma_5_4 (L H K d n : ℕ) (hH : 1 ≤ H) (hK : 1 ≤ K) (hd : d + H ≤ L) (hn1 : 1 ≤ n)
    (hn2 : n ≤ 2 ^ L) (v : Leaf d) :
    (QCapMean 3 H K).toReal - K * 2 ^ H * Real.exp (-((n * (2 : ℝ)⁻¹ ^ d) / 2 ^ H)) -
        3 * K * (n * (2 : ℝ)⁻¹ ^ d) * (2 : ℝ)⁻¹ ^ d ≤
      mean (fun ω : Labels (2 ^ L) (2 ^ L) => regionF L H K n ω v.toList) := by sorry

end PathORAMCap
