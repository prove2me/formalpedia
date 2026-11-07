-- Prove2me | Theorems.Thm_RandOrderSort_eq_22
-- name    : RandOrderSort.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:03.465424+00:00
-- url     : https://prove2.me/theorems/bc9a0d4f-518c-4acc-90a0-1e035fd4f787
-- title:
--   Display (22) — replacement charges bounded by overflow witnesses
-- statement:
--   Let $n\ge 8192$ and $\kappa=2048$. For every operation of every phase of every execution, with $b$ the current number of buckets, and every cut $q$ of the strict key order,
--   $$D_{\mathrm{op}}(q)\le\kappa+4096\sum_{\substack{s\in\{1,2,4,\dots\}\\ 2s\le b}}s\mathbf 1[E_s(q)],$$
--   where $E_s(q)$ is the event that a child, with $s$ leaves, of the selected $2s$-leaf parent locally overflows.
--
--   This is the witness bound behind (40) and (50).
--
--   Differences from the source:
--   - encoding: a cut q → a rank cut c ≤ n of the strict key order (`rankCut`); reason: as in Lemma 4.1
--   - encoding: the sum over s ∈ {1, 2, 4, …} with 2s ≤ b → the sum over s = 2^h, h < n, with 2^(h+1) ≤ b; reason: b ≤ n, so this range contains every such scale
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §4.1.2, eq. (22), p.22

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

open Classical in
/-- **Display (22)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), §4.1.2, p.22: "Summing over all scales and adding the leaf bound gives
D_op(q) ≤ κ + 4096 ∑_{s∈{1,2,4,...}, 2s≤b} s 1[E_s(q)]. (22) Here b is the current number of buckets."

**Formalization Note.** For every operation of every phase `p < L + k` of every execution with
`n ≥ 8192`, and every cut of the strict key order. A scale is `s = 2^h` with `2s ≤ b`; `E_s` is `Es` (a child of the selected
`2s`-leaf parent locally overflows). The sum over `h < n` contains every scale with `2s ≤ b`. -/
theorem eq_22 : ∀ n, 16 * T ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (c : ℕ), c ≤ n →
    ∀ p < numPhases n, ∀ arr : Bool,
      (Dop (rankCut n (ltOf x π σ) c) (opReqs (runOf x π σ) p arr) : ℝ) ≤
        (kappa : ℝ) + 4096 * ∑ h ∈ Finset.range n,
          (if 2 ^ (h + 1) ≤ phaseLeaves n p ∧
              Es (rankCut n (ltOf x π σ) c) (phaseTree n (ltOf x π σ) p)
                (opReqs (runOf x π σ) p arr) (phaseCap n p) h
            then (2 : ℝ) ^ h else 0) := by sorry

end RandOrderSort
