-- Prove2me | Theorems.Thm_PathORAMCap_theorem_1_2
-- name    : PathORAMCap.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:24.736323+00:00
-- url     : https://prove2.me/theorems/7a152b45-c9e3-427d-a643-f6c5950d5668
-- title:
--   Theorem 1.2 — capacity four: $\mathbb P[S(\pi;s)>R]\le\frac{23}{28}(5/7)^R\le e^{-R\log(7/5)}$
-- statement:
--   For every integer $N\ge1$, every instance $(s,\alpha)$ of $P_{4,N}$ and every integer $R\ge0$, the execution $\pi=P_{4,N}(s,\alpha)$ satisfies
--
--   $$\mathbb P\bigl[S(\pi;s)>R\bigr]\le\frac{23}{28}\Bigl(\frac57\Bigr)^R\le\exp\bigl(-R\log(7/5)\bigr).$$
--
--   So capacity four admits a uniform exponential stash tail bound with $C=1$ and $c=\log(7/5)$, improving the previously proved capacity five.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Theorem 1.2, p.8 (PDF p.11), eq. (3); restated p.13 (PDF p.16)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Theorem 1.2** (Sufficiency of Capacity Four; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.8 (PDF p.11), restated p.13): "For every
integer N ≥ 1, every instance (s, α) of P4,N, and every integer R ≥ 0, the execution π = P4,N(s, α)
satisfies P[S(π; s) > R] ≤ (23/28)(5/7)^R ≤ exp(−R log(7/5)). (3)"

**Formalization Note.** Both inequalities of the chain are conjuncts. -/
theorem theorem_1_2 (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : 1 ≤ s) (α : Fin s → Fin N) (R : ℕ) :
    probability (fun ω : Labels N s => R < stashSize 4 α ω s) ≤ 23 / 28 * (5 / 7 : ℝ) ^ R ∧
      23 / 28 * (5 / 7 : ℝ) ^ R ≤ Real.exp (-(R * Real.log (7 / 5))) := by sorry

end PathORAMCap
