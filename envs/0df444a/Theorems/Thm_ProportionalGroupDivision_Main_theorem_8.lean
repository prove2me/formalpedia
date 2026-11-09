-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_8
-- name    : ProportionalGroupDivision.Main.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:56.321101+00:00
-- url     : https://prove2.me/theorems/6a9a1ff5-d278-4e87-b7be-7ac56f76e604
-- title:
--   Theorem 8 — a full allocation with $|\langle A^i_j,v_i\rangle-\langle A^i_j,\mathbf 1/k\rangle|\le C'\,\Xi(n_1/d,r)\sqrt{\Delta^i_j}$
-- statement:
--   Let $C$ be a constant from Theorem 6 and $\Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)}$. There is an absolute constant $C'>0$ such that the following holds. Let $n_1\ge\dots\ge n_k\ge1$ be the group sizes (the standing assumption of Section 2) and suppose the agents' valuations are given by matrices $A^1\in[0,1]^{n_1\times m},\dots,A^k\in[0,1]^{n_k\times m}$ that are $(\Delta^1_j),\dots,(\Delta^k_j)$-structured, with $\Delta^i_j>0$. Let $r$ be an upper bound on every ratio, $r\ge\Delta^i_j/\Delta^{i'}_{j'}$, and let $d>0$ be a lower bound $d\le\min(n_1,\min_{i,j}\Delta^i_j)$. Then there is an allocation $v_1,\dots,v_k\in\{0,1\}^m$, $\sum_i v_i=\mathbf 1$, such that for every $i\in[k]$ and $j\in[n_i]$
--
--   $$\big|\langle A^i_j,v_i\rangle-\langle A^i_j,\mathbf 1/k\rangle\big|\ \le\ C'\cdot\Xi(n_1/d,\,r)\cdot\sqrt{\Delta^i_j}.$$
--
--   The constant $C'$ is chosen before $k$, the sizes, $m$ and the matrices. This is the high-level partition of the goods in the proof of the upper bound of Theorem 4.
--
--   Differences from the source:
--   - reading: Ξ with C the constant from Theorem 6 → every C with the property of Theorem 6 (hypothesis TopDownBound C); reason: Ξ is defined from "a constant from Theorem 6"; any constant with that property is such a constant, and Theorem 6 provides one
--   - generalization: k ≥ 2 (Section 2 proves the upper bound of Theorem 4) → every k ≥ 1; reason: the proof of Theorem 8 treats k = 1 explicitly as its base case; the statement specializes to k ≥ 2
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: allocation v_1, …, v_k ∈ {0,1}^m with Σ v_i = 1 → a map σ from goods to groups, v_i the indicator of σ⁻¹(i); reason: the same partitions
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 8 and the standing assumptions of Section 2, PDF p. 7 = printed p. 7; proof PDF pp. 8–9

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Theorem 8 (PDF p. 7), with `Ξ` built from a constant `C` of Theorem 6 (`TopDownBound C`):
there is an absolute constant `C′ > 0` such that the following holds. Let `n_1 ≥ ⋯ ≥ n_k ≥ 1`
(the standing assumption of Section 2, `k ≥ 1`) and let the valuations be given by
`(Δ^i_j)`-structured matrices `A^i ∈ [0,1]^{n_i×m}` with `Δ^i_j > 0`. Let `r` be an upper bound on
every ratio `Δ^i_j/Δ^{i′}_{j′}` and `d > 0` a lower bound `d ≤ min(n_1, min_{i,j} Δ^i_j)`. Then there
is an allocation `v_1, …, v_k ∈ {0,1}^m`, `∑ v_i = 𝟙` (a map `σ : Fin m → Fin k`), such that for every
`i ∈ [k]`, `j ∈ [n_i]`: `|⟨A^i_j, v_i⟩ − ⟨A^i_j, 𝟙/k⟩| ≤ C′ · Ξ(n_1/d, r) · √Δ^i_j`. -/
theorem theorem_8 (C : ℝ) (hC : TopDownBound C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (k : ℕ) (hk : 0 < k) (n : Fin k → ℕ), Antitone n → (∀ i, 0 < n i) →
      ∀ (m : ℕ) (A : GroupMatrices n m) (Δ : (i : Fin k) → Fin (n i) → ℝ),
        (∀ i, IsStructured (A i) (Δ i)) →
      ∀ r d : ℝ, (∀ (i : Fin k) (j : Fin (n i)) (i' : Fin k) (j' : Fin (n i')),
          Δ i j / Δ i' j' ≤ r) →
        0 < d → d ≤ (n ⟨0, hk⟩ : ℝ) → (∀ (i : Fin k) (j : Fin (n i)), d ≤ Δ i j) →
        ∃ σ : Fin m → Fin k, ∀ (i : Fin k) (j : Fin (n i)),
          |rowGain A σ i j - rowShare A i j| ≤
            C' * Xi C ((n ⟨0, hk⟩ : ℝ) / d) r * Real.sqrt (Δ i j) := by sorry

end ProportionalGroupDivision.Main
