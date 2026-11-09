-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_9
-- name    : ProportionalGroupDivision.Main.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:06.341895+00:00
-- url     : https://prove2.me/theorems/69606aab-2579-4a08-9874-207d44987d7d
-- title:
--   Theorem 9 — joint gifting to all groups: at most $(C'\Upsilon+1)\sqrt{nk}$ goods
-- statement:
--   Let $C'>0$, let $n_1\ge\dots\ge n_k\ge1$ be the group sizes (Section 2), $n=n_1+\dots+n_k$, and let $A^1\in[0,1]^{n_1\times m},\dots,A^k\in[0,1]^{n_k\times m}$ be the agents' valuations. Let $\Upsilon=\Xi(n_1k/n,n_1k/n)$ with $\Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)}$. Then there is a partial assignment of goods to groups $v_1,\dots,v_k\in\{0,1\}^m$, $\sum_i v_i\le\mathbf 1$, such that, with $l=\langle\mathbf 1,v_1+\dots+v_k\rangle$ and $\hat A^i\in[0,1]^{n_i\times(m-l)}$ the matrix $A^i$ with all assigned columns removed:
--
--   1. $l\le(C'\Upsilon+1)\cdot\sqrt{n\cdot k}$;
--   2. for every group $i$ there are a permutation $p^i_1,\dots,p^i_{n_i}$ of its agents and values $n_1\ge\Delta^i_{p^i_1}\ge\dots\ge\Delta^i_{p^i_{n_i}}\ge n/k$ such that the matrix $B^i$ with rows $\hat A^i_{p^i_1},\dots,\hat A^i_{p^i_{n_i}}$ is $(\Delta^i_{p^i_1},\dots,\Delta^i_{p^i_{n_i}})$-structured and every agent $j\in[n_i]$ satisfies
--
--   $$\max\Big(\langle A^i_j,v_i\rangle,\ C'\Upsilon\sqrt{n/k}\Big)\ \ge\ C'\Upsilon\sqrt{\Delta^i_j}.$$
--
--   The same set of assigned columns is removed from every group's matrix. Together with Theorem 8 on the residual matrices this gives the upper bound of Theorem 4.
--
--   Differences from the source:
--   - generalization: Υ = Ξ(n_1k/n, n_1k/n) with C the constant from Theorem 6 → every constant C > 0 in Ξ; reason: the argument does not use the property of Theorem 6; the statement specializes to the paper's C, which is positive
--   - generalization: k ≥ 2 (Section 2 proves the upper bound of Theorem 4) → every k ≥ 1; reason: the statement and its proof do not use k ≥ 2; it specializes to k ≥ 2
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: v_1, …, v_k ∈ {0,1}^m with Σ v_i ≤ 1; Â^i ∈ [0,1]^{n_i×(m−l)} → a map w from goods to Option groups (w g = some i iff g is assigned to group i); Â^i has the unassigned goods as its column index type; reason: the same objects up to relabelling the remaining columns
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 9 and the standing assumptions of Section 2, PDF pp. 9–10 = printed pp. 9–10

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Theorem 9 (PDF pp. 9–10): let `C′ > 0`, let `n_1 ≥ ⋯ ≥ n_k ≥ 1` (Section 2), `n = n_1 + ⋯ + n_k`,
`Υ = Ξ(n_1k/n, n_1k/n)`, and let `A^i ∈ [0,1]^{n_i×m}` be the agents' valuations. Then there is a
partial assignment `v_1, …, v_k ∈ {0,1}^m`, `∑ v_i ≤ 𝟙` (a map `w : Fin m → Option (Fin k)`,
`w g = some i` iff good `g` is assigned to group `i`), such that, with `l` the number of assigned
goods and `Â^i` the matrix `A^i` with all assigned columns removed,
(1) `l ≤ (C′Υ + 1)√(n · k)`;
(2) for every group `i` there are a permutation `p^i` of its agents and values
`n_1 ≥ Δ^i_{p^i_1} ≥ ⋯ ≥ Δ^i_{p^i_{n_i}} ≥ n/k` such that `B^i` (rows `Â^i_{p^i_1}, …, Â^i_{p^i_{n_i}}`)
is `(Δ^i_{p^i_1}, …, Δ^i_{p^i_{n_i}})`-structured and every agent `j ∈ [n_i]` satisfies
`max(⟨A^i_j, v_i⟩, C′Υ√(n/k)) ≥ C′Υ√Δ^i_j`. -/
theorem theorem_9 (C C' : ℝ) (hC : 0 < C) (hC' : 0 < C') (k : ℕ) (hk : 0 < k)
    (n : Fin k → ℕ) (hmono : Antitone n) (hpos : ∀ i, 0 < n i) (m : ℕ) (A : GroupMatrices n m)
    (hA : IsUnitEntries A) :
    ∃ w : Fin m → Option (Fin k),
      (((Finset.univ.filter (fun g => w g ≠ none)).card : ℝ) ≤
        (C' * Xi C ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ)) ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ))
            + 1) * Real.sqrt ((∑ i, (n i : ℝ)) * k)) ∧
      ∀ i : Fin k, ∃ (p : Equiv.Perm (Fin (n i))) (Δ : Fin (n i) → ℝ),
        (∀ ℓ, Δ (p ℓ) ≤ n ⟨0, hk⟩ ∧ (∑ i, (n i : ℝ)) / k ≤ Δ (p ℓ)) ∧ Antitone (Δ ∘ p) ∧
        IsStructured (fun (ℓ : Fin (n i)) (g : {g : Fin m // w g = none}) => A i (p ℓ) g)
          (Δ ∘ p) ∧
        ∀ j : Fin (n i),
          C' * Xi C ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ))
              ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ)) * Real.sqrt (Δ j) ≤
            max (∑ g ∈ Finset.univ.filter (fun g => w g = some i), A i j g)
              (C' * Xi C ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ))
                ((n ⟨0, hk⟩ : ℝ) * k / ∑ i, (n i : ℝ)) * Real.sqrt ((∑ i, (n i : ℝ)) / k)) := by sorry

end ProportionalGroupDivision.Main
