-- Prove2me | Theorems.Thm_PathORAMCap_theorem_1_3
-- name    : PathORAMCap.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:09.87335+00:00
-- url     : https://prove2.me/theorems/dcb0d927-089c-4614-8e7a-d7c50bcfd28e
-- title:
--   Theorem 1.3 — capacity three fails: $\mathbb E[S]>N/2^{18}+3$, $\mathbb P[S>N/2^{19}]>1/(2^{19}-1)$
-- statement:
--   For every integer $L\ge49$, let $N=2^L$, $\alpha=(1,\dots,N)$ and $\pi=P_{3,N}(N,\alpha)$. Then
--
--   $$\mathbb E[S(\pi;N)]>\frac{N}{2^{18}}+3,\qquad \mathbb P\bigl[S(\pi;N)>N/2^{19}\bigr]>\frac1{2^{19}-1}.$$
--
--   Consequently the family $\{P_{3,N}:N\ge1\}$ does not admit a uniform exponential stash tail bound.
--
--   A stash budget proportional to the database size is exceeded with a probability bounded away from zero, which no uniform exponential tail allows.
--
--   Differences from the source:
--
--   - encoding: all initial and new leaf labels independent and uniform → the uniform law on the finite label space Labels N s = (Fin N → Leaf L) × (Fin s → Leaf L), with P and E the uniform probability and mean; reason: the labels are the only random inputs of the execution, and independent uniform labels are exactly the uniform law on this product
--   - encoding: logical addresses [N] = {1, …, N} and α ∈ [N]^s → blocks Fin N (address i is i − 1) and α : Fin s → Fin N; reason: an order-preserving relabeling, so the smallest-identifier tie-break is unchanged
--   - encoding: block values, reads and writes, encryption and dummy padding → not modelled; the state is the position map, the created blocks and each block's bucket (or the stash); reason: they do not affect which real blocks sit where, and S counts real blocks only
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Theorem 1.3, p.9 (PDF p.12), eq. (4); restated p.36 (PDF p.39)

import Mathlib
import Definitions.Def_PathORAMCap_HasUEST

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Theorem 1.3** (Insufficiency of Capacity Three; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.9 (PDF p.12), restated p.36): "For
every integer L ≥ 49, let N = 2^L, let α = (1, . . . , N), and let π = P3,N(N, α). Then
E[S(π; N)] > N/2^18 + 3, P[S(π; N) > N/2^19] > 1/(2^19 − 1). (4) Consequently, the family
{P3,N : N ≥ 1} does not admit a uniform exponential stash tail bound."

**Formalization Note.** Three conjuncts: the two inequalities for every `L ≥ 49` (the scan
`α = id : Fin N → Fin N`, `s = N`), and `¬ HasUEST 3`. -/
theorem theorem_1_3 :
    (∀ L : ℕ, 49 ≤ L →
      (2 : ℝ) ^ L / 2 ^ 18 + 3 <
          mean (fun ω : Labels (2 ^ L) (2 ^ L) => (stashSize 3 (fun i => i) ω (2 ^ L) : ℝ)) ∧
        1 / ((2 : ℝ) ^ 19 - 1) <
          probability (fun ω : Labels (2 ^ L) (2 ^ L) =>
            (2 : ℝ) ^ L / 2 ^ 19 < stashSize 3 (fun i => i) ω (2 ^ L))) ∧
      ¬ HasUEST 3 := by sorry

end PathORAMCap
