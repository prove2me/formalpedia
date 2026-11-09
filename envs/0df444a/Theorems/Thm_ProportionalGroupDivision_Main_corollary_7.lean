-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_corollary_7
-- name    : ProportionalGroupDivision.Main.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:46.965707+00:00
-- url     : https://prove2.me/theorems/816df8d5-c3ec-49aa-b277-628f2db1438a
-- title:
--   Corollary 7 — simultaneous rounding of $k$ structured matrices with error $\Xi(\max\{1,n/d\},r)\sqrt{k\Delta^i_j}$
-- statement:
--   Let $C$ be a constant from Theorem 6 and $\Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)}$. Let $n_1,\dots,n_k$ and $m$ be positive integers and let $A^1\in[0,1]^{n_1\times m},\dots,A^k\in[0,1]^{n_k\times m}$ be $(\Delta^1_j),\dots,(\Delta^k_j)$-structured respectively, with $\Delta^i_j>0$. Let
--
--   $$r=\max_{i,j,i',j'}\frac{\Delta^i_j}{\Delta^{i'}_{j'}},\qquad d=\min_{i,j}\Delta^i_j .$$
--
--   Then for every $x_0\in[0,1]^m$ there is $x\in\{0,1\}^m$ such that for all $i\in[k]$, $j\in[n_i]$
--
--   $$|\langle A^i_j,x_0-x\rangle|\ \le\ \Xi\big(\max\{1,(n_1+\dots+n_k)/d\},\,r\big)\cdot\sqrt{k\,\Delta^i_j}.$$
--
--   One binary vector serves all $k$ matrices at the cost of a factor $\sqrt k$; this is the splitting step of Theorem 8.
--
--   Differences from the source:
--   - reading: Ξ with C the constant from Theorem 6 → every C with the property of Theorem 6 (hypothesis TopDownBound C); reason: Ξ is defined from "a constant from Theorem 6"; any constant with that property is such a constant, and Theorem 6 provides one
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: r the maximum ratio and d the minimum of the Δ^i_j → r is the greatest element of the set of ratios and d the least element of the set of values (IsGreatest, IsLeast); reason: the same numbers; no junk value of a real max/min
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Corollary 7, PDF p. 6 = printed p. 6; restated as Corollary 23, PDF p. 21

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Corollary 7 (PDF p. 6; restated as Corollary 23, p. 21), with `Ξ` built from a constant `C`
of Theorem 6 (`TopDownBound C`): let `n_1, …, n_k` and `m` be positive integers and let
`A^i ∈ [0,1]^{n_i×m}` be `(Δ^i_j)`-structured with `Δ^i_j > 0`. Let `r = max_{i,j,i′,j′} Δ^i_j/Δ^{i′}_{j′}`
and `d = min_{i,j} Δ^i_j`. Then for every `x₀ ∈ [0,1]^m` there is `x ∈ {0,1}^m` with, for all `i, j`,
`|⟨A^i_j, x₀ − x⟩| ≤ Ξ(max{1, (n_1 + ⋯ + n_k)/d}, r) · √(k Δ^i_j)`. -/
theorem corollary_7 (C : ℝ) (hC : TopDownBound C) (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i) (A : GroupMatrices n m)
    (Δ : (i : Fin k) → Fin (n i) → ℝ) (hA : ∀ i, IsStructured (A i) (Δ i)) (r d : ℝ)
    (hr : IsGreatest {q : ℝ | ∃ (i : Fin k) (j : Fin (n i)) (i' : Fin k) (j' : Fin (n i')),
      q = Δ i j / Δ i' j'} r)
    (hd : IsLeast {q : ℝ | ∃ (i : Fin k) (j : Fin (n i)), q = Δ i j} d)
    (x₀ : Fin m → ℝ) (hx₀ : ∀ g, x₀ g ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x : Fin m → ℝ, (∀ g, x g = 0 ∨ x g = 1) ∧
      ∀ (i : Fin k) (j : Fin (n i)),
        |∑ g, A i j g * (x₀ g - x g)| ≤
          Xi C (max 1 ((∑ i, (n i : ℝ)) / d)) r * Real.sqrt ((k : ℝ) * Δ i j) := by sorry

end ProportionalGroupDivision.Main
