-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_lemma_17
-- name    : ProportionalGroupDivision.Main.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:57.765722+00:00
-- url     : https://prove2.me/theorems/a8ccfe13-9f0f-4583-97cd-75c3fb2b00a1
-- title:
--   Lemma 17 — at most $m/t$ rows of a $(\Delta_i)$-structured matrix are $t$-heavy
-- statement:
--   Let $n,m\in\mathbb N$, let $A\in[0,1]^{n\times m}$ be $(\Delta_i)$-structured, and let $r\ge1$ with $\Delta_1/\Delta_n\le r$. Then for every $t>0$ the number of rows $i$ with
--
--   $$\|A_i\|_1\ \ge\ 2\,t\,(\log_2 r+2)\,\Delta_i \tag{6}$$
--
--   is at most $m/t$.
--
--   This counting bound on heavy rows is what makes the partial-coloring thresholds of Theorem 6 admissible.
--
--   Differences from the source:
--   - encoding: Δ_1/Δ_n ≤ r for rows 1, …, n → Δ ⟨0⟩ / Δ ⟨N−1⟩ ≤ r, required when N > 0; rows Fin N; reason: 0-based indices; for N = 0 there are no rows and the bound is trivial
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Lemma 17, PDF p. 18 = printed p. 18

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Lemma 17 (PDF p. 18): let `A ∈ [0,1]^{N×m}` be `(Δ_i)`-structured with `Δ_1/Δ_N ≤ r` for some
`r ≥ 1`. Then for every `t > 0` the number of rows `i` with `‖A_i‖₁ ≥ 2 · t · (log₂ r + 2) · Δ_i`
is at most `m/t`. (`Δ_1 = Δ ⟨0, _⟩`, `Δ_N = Δ ⟨N − 1, _⟩`; the ratio condition is required when
`N > 0`.) -/
theorem lemma_17 (N m : ℕ) (A : Matrix (Fin N) (Fin m) ℝ) (Δ : Fin N → ℝ)
    (hA : IsStructured A Δ) (r : ℝ) (hr : 1 ≤ r)
    (hratio : ∀ hN : 0 < N, Δ ⟨0, hN⟩ / Δ ⟨N - 1, by omega⟩ ≤ r) (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter
        (fun i : Fin N => 2 * t * (Real.logb 2 r + 2) * Δ i ≤ ∑ g, |A i g|)).card : ℝ) ≤
      (m : ℝ) / t := by sorry

end ProportionalGroupDivision.Main
