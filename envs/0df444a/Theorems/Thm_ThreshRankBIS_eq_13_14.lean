-- Prove2me | Theorems.Thm_ThreshRankBIS_eq_13_14
-- name    : ThreshRankBIS.eq_13_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:47.357948+00:00
-- url     : https://prove2.me/theorems/f5576d6e-ab29-4e7e-893c-631626fcfbd8
-- title:
--   Displays (13)–(14) — $\sum_{j\le\min\{m,\lfloor L\rfloor\}}\binom mj\le z^{-L}(1+z)^m\le z^{-L}e^{mz}$
-- statement:
--   For an integer $m\ge0$, a real $L\ge0$ and $0<z\le1$,
--
--   $$
--   \sum_{j=0}^{\min\{m,\lfloor L\rfloor\}}\binom mj\le z^{-L}(1+z)^m\le z^{-L}e^{mz}. \tag{13}
--   $$
--
--   If $m\le M$ and $0<h\le M$ (real $M$, $h$), then
--
--   $$
--   \sum_{j=0}^{\min\{m,\lfloor h\rfloor\}}\binom mj\le\exp\{h\log(eM/h)\}. \tag{14}
--   $$
--
--   This elementary subset estimate counts the witness sets of the greedy deletion, refinement and recovery steps; with $z=e^{-ad}$ it turns $\mathrm{poly}$-size witness budgets into the factor $e^{v_d}$.
--
--   Differences from the source: none.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §4.2, p.13, displays (13) and (14)

import Mathlib
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Displays (13) and (14)**, p.13 (the elementary subset estimate). For an integer `m ≥ 0`, a
real `L ≥ 0` and `0 < z ≤ 1`,
`∑_{j=0}^{min{m,⌊L⌋}} binom(m, j) ≤ z^{−L}(1 + z)^m ≤ z^{−L} e^{mz}` (13).
If `m ≤ M` and `0 < h ≤ M` (reals `M`, `h`), then
`∑_{j=0}^{min{m,⌊h⌋}} binom(m, j) ≤ exp{h log(eM/h)}` (14).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §4.2, p.13,
displays (13) and (14).

**Formalization Note.** `z^{−L}` is the real power `z ^ (-L)`; `⌊L⌋` is `Nat.floor` (`L ≥ 0`). -/
theorem eq_13_14 :
    (∀ (m : ℕ) (L z : ℝ), 0 ≤ L → 0 < z → z ≤ 1 →
      (∑ j ∈ range (min m ⌊L⌋₊ + 1), (m.choose j : ℝ)) ≤ z ^ (-L) * (1 + z) ^ m ∧
        z ^ (-L) * (1 + z) ^ m ≤ z ^ (-L) * Real.exp (m * z)) ∧
    (∀ (m : ℕ) (M h : ℝ), (m : ℝ) ≤ M → 0 < h → h ≤ M →
      (∑ j ∈ range (min m ⌊h⌋₊ + 1), (m.choose j : ℝ)) ≤
        Real.exp (h * Real.log (Real.exp 1 * M / h))) := by sorry

end ThreshRankBIS
