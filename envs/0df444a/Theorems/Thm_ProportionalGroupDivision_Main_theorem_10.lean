-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_10
-- name    : ProportionalGroupDivision.Main.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:00.349276+00:00
-- url     : https://prove2.me/theorems/c282467b-050a-46c4-a49f-85be272e78f0
-- title:
--   Theorem 10 — one-group gifting: few gifted goods, structured residual, compensated agents
-- statement:
--   Let $C'>0$ be a real and $n,n_1,k>0$ integers with $n\ge n_1\ge n/k$. Let $A\in[0,1]^{n_s\times m}$ be the valuations of the agents of a group with $n_s\le n_1$ agents, and let
--
--   $$\Upsilon=\Xi\Big(\frac{n_1k}{n},\frac{n_1k}{n}\Big),\qquad \Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)} .$$
--
--   Then there is a partial assignment $v\in\{0,1\}^m$ such that, with $l=\langle\mathbf 1,v\rangle$ the number of assigned goods and $A'\in[0,1]^{n_s\times(m-l)}$ the matrix $A$ with the assigned columns removed:
--
--   1. $l\le(C'\Upsilon+1)\cdot n_s\cdot\sqrt{k/n}$;
--   2. there are a permutation $p_1,\dots,p_{n_s}$ of the agents and values $n_1\ge\Delta_{p_1}\ge\dots\ge\Delta_{p_{n_s}}\ge n/k$ such that the matrix $B$ with rows $A'_{p_1},\dots,A'_{p_{n_s}}$ is $(\Delta_{p_1},\dots,\Delta_{p_{n_s}})$-structured and every agent $j\in[n_s]$ satisfies
--
--   $$\max\Big(\langle A_j,v\rangle,\ C'\Upsilon\sqrt{n/k}\Big)\ \ge\ C'\Upsilon\sqrt{\Delta_j}.$$
--
--   Theorem 9 applies this to each group in turn.
--
--   Differences from the source:
--   - generalization: Υ = Ξ(n_1k/n, n_1k/n) with C the constant from Theorem 6 → every constant C > 0 in Ξ; reason: the argument does not use the property of Theorem 6; the statement specializes to the paper's C, which is positive
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: v ∈ {0,1}^m and A′ ∈ [0,1]^{n_s×(m−l)} → v a set of goods; A′ has the ungifted goods as its column index type; reason: the same objects up to relabelling the m − l remaining columns
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 10, PDF p. 11 = printed p. 11; proof PDF pp. 12–15

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Theorem 10 (PDF p. 11): let `C′ > 0` be a real and `n, n_1, k > 0` integers with
`n ≥ n_1 ≥ n/k`; let `A ∈ [0,1]^{ns×m}` be the valuations of a group with `ns ≤ n_1` agents, and
`Υ = Ξ(n_1k/n, n_1k/n)`. Then there is a partial assignment `v ∈ {0,1}^m` (the set of assigned
goods) such that, with `l = ⟨𝟙, v⟩` and `A′` the matrix `A` with the assigned columns removed,
(1) `l ≤ (C′Υ + 1) · ns · √(k/n)`;
(2) there are a permutation `p` of the agents and values `n_1 ≥ Δ_{p_1} ≥ ⋯ ≥ Δ_{p_{ns}} ≥ n/k`
such that `B` (rows `A′_{p_1}, …, A′_{p_{ns}}`) is `(Δ_{p_1}, …, Δ_{p_{ns}})`-structured and every
agent `j` satisfies `max(⟨A_j, v⟩, C′Υ√(n/k)) ≥ C′Υ√Δ_j`. -/
theorem theorem_10 (C C' : ℝ) (hC : 0 < C) (hC' : 0 < C') (n n₁ k : ℕ) (hn : 0 < n)
    (hn₁ : 0 < n₁) (hk : 0 < k) (h₁ : n₁ ≤ n) (h₂ : (n : ℝ) / k ≤ n₁) (ns m : ℕ)
    (hns : ns ≤ n₁) (A : Matrix (Fin ns) (Fin m) ℝ) (hA : ∀ i g, 0 ≤ A i g ∧ A i g ≤ 1) :
    ∃ v : Finset (Fin m),
      (v.card : ℝ) ≤ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n) + 1) * ns *
        Real.sqrt ((k : ℝ) / n) ∧
      ∃ (p : Equiv.Perm (Fin ns)) (Δ : Fin ns → ℝ),
        (∀ ℓ, Δ (p ℓ) ≤ n₁ ∧ (n : ℝ) / k ≤ Δ (p ℓ)) ∧ Antitone (Δ ∘ p) ∧
        IsStructured (fun (ℓ : Fin ns) (g : {g : Fin m // g ∉ v}) => A (p ℓ) g) (Δ ∘ p) ∧
        ∀ j : Fin ns,
          C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n) * Real.sqrt (Δ j) ≤
            max (∑ g ∈ v, A j g)
              (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n) * Real.sqrt ((n : ℝ) / k)) := by sorry

end ProportionalGroupDivision.Main
