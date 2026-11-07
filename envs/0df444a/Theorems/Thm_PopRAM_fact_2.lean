-- Prove2me | Theorems.Thm_PopRAM_fact_2
-- name    : PopRAM.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:57.457141+00:00
-- url     : https://prove2.me/theorems/62c8f4c7-f93c-4012-82bc-0d9365551025
-- title:
--   Fact 2 — $\log n_w=w+O(\log w)=\Theta(w)$ and $\log n_w<2w$ for large $w$
-- statement:
--   Let $\mathcal P$ be a $\mathcal P$-program and $C\ge2$ an integer. Then
--
--   1. there is a constant $K$ with
--   $$w\le\log_2 n_w\le w+K\log_2(w+1)\qquad\text{for all }w\ge1;$$
--   2. $\log_2 n_w<2w$ for all sufficiently large $w$.
--
--   So $\log n_w=\Theta(w)$: the word length is logarithmic in the population, which is what every subprotocol's timing relies on.
--
--   Differences from the source:
--   - encoding: w + O(log w) → w ≤ log₂ n_w ≤ w + K log₂(w + 1) for w ≥ 1; reason: log₂(w + 1) makes the error term meaningful at w = 1; Θ(w) follows
--   - encoding: C > 1 a fixed integer constant → every integer C ≥ 2; reason: the integers above 1
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Fact 2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PopRAM_PProgram

set_option autoImplicit false

namespace PopRAM

/-- **Fact 2** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version sha256 f13223b3…,
p.6, PDF p.7). "We have log n_w = w + O(log w) = Θ(w) and, in particular, log n_w < 2w for all
sufficiently large w."

For every P-program and every integer `C ≥ 2`:
1. there is `K` with `w ≤ log₂ n_w ≤ w + K log₂(w + 1)` for all `w ≥ 1`;
2. `log₂ n_w < 2w` for all sufficiently large `w`.

**Formalization Note** Logarithms are base 2 (p.1). `w + O(log w)` is written with `log₂(w + 1)` so
that it is meaningful at `w = 1`; `Θ(w)` follows from (1). -/
theorem fact_2 (P : PProgram) (C : ℕ) (hC : 2 ≤ C) :
    (∃ K : ℝ, ∀ w : ℕ, 1 ≤ w →
      (w : ℝ) ≤ Real.logb 2 (P.nPop C w) ∧
      Real.logb 2 (P.nPop C w) ≤ w + K * Real.logb 2 (w + 1)) ∧
    ∃ w₀ : ℕ, ∀ w ≥ w₀, Real.logb 2 (P.nPop C w) < 2 * w := by sorry

end PopRAM
