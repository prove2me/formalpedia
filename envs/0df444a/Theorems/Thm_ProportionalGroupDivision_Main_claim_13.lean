-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_claim_13
-- name    : ProportionalGroupDivision.Main.claim_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:28.668216+00:00
-- url     : https://prove2.me/theorems/a110af70-7dc0-4163-8b78-0eef11d9135c
-- title:
--   Claim 13 — every agent is compensated: $\max(\langle A_i,v\rangle,C'\Upsilon\sqrt{n/k})\ge C'\Upsilon\sqrt{\Delta_i}$
-- statement:
--   Throughout, $C'>0$ is a real, $n,n_1,k>0$ are integers with $n\ge n_1\ge n/k$, $A\in[0,1]^{n_s\times m}$ are the valuations of a group with $n_s\le n_1$ agents, and
--
--   $$\Upsilon=\Xi\Big(\frac{n_1k}{n},\frac{n_1k}{n}\Big),\qquad \Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)} .$$
--
--   Algorithm 1 is run with removal threshold $C'\Upsilon\sqrt\lambda$ and stopping level $n/k$.
--
--   Let $v$ be the output of the gifting algorithm and $\Delta_i$ as in Claim 12. Then every agent $i\in[n_s]$ satisfies
--
--   $$\max\Big(\langle A_i,v\rangle,\ C'\cdot\Upsilon\cdot\sqrt{n/k}\Big)\ \ge\ C'\cdot\Upsilon\cdot\sqrt{\Delta_i}. \tag{4}$$
--
--   The gifted value may be arbitrarily large; only this lower bound is asserted. This is the compensation half of part (2) of Theorem 10.
--
--   Differences from the source:
--   - generalization: Υ = Ξ(n_1k/n, n_1k/n) with C the constant from Theorem 6 → every constant C > 0 in Ξ; reason: the argument does not use the property of Theorem 6; the statement specializes to the paper's C, which is positive
--   - generalization: Algorithm 1 with arg max and "in any order" left unresolved → every tie-breaking priority τ of goods and agents (a universally quantified parameter); reason: the claim is asserted for every way of resolving the ties, which includes any particular one
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: Algorithm 1 run until it terminates, with a dummy good valued 0 by everyone (p. 12); v ∈ {0,1}^m; Δ_i, p and B as defined on p. 14 → giftRun, the state after n_s + m + 1 rounds of giftStep (every non-final round removes an agent or gifts a new good, so the run has terminated); the dummy good as the value 0 inserted in the maximum defining λ; v the set giftedSet; Δ = giftDelta, p = giftPerm, B = giftResidual with the ungifted goods as column type; reason: the same run and the same constructed objects
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Claim 13, PDF p. 15 = printed p. 15

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured
import Definitions.Def_ProportionalGroupDivision_Main_Gifting

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Claim 13 (PDF p. 15): in the setting of Theorem 10, with `v` the output of Algorithm 1 and
`Δ_i` as in Claim 12, every agent `i ∈ [ns]` satisfies
`max(⟨A_i, v⟩, C′ · Υ · √(n/k)) ≥ C′ · Υ · √Δ_i` (4). The ties left open by the paper (`arg max`, "in any order") are resolved by an arbitrary priority
`τ`; the claim holds for every `τ`. -/
theorem claim_13 (C C' : ℝ) (hC : 0 < C) (hC' : 0 < C') (n n₁ k : ℕ) (hn : 0 < n)
    (hn₁ : 0 < n₁) (hk : 0 < k) (h₁ : n₁ ≤ n) (h₂ : (n : ℝ) / k ≤ n₁) (ns m : ℕ)
    (hns : ns ≤ n₁) (A : Matrix (Fin ns) (Fin m) ℝ) (hA : ∀ i g, 0 ≤ A i g ∧ A i g ≤ 1)
    (τ : TieOrder ns m) :
    ∀ i : Fin ns,
      C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n) *
          Real.sqrt (giftDelta τ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n)) ((n : ℝ) / k) A i) ≤
        max (∑ g ∈ giftedSet τ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n)) ((n : ℝ) / k) A,
              A i g)
          (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n) * Real.sqrt ((n : ℝ) / k)) := by sorry

end ProportionalGroupDivision.Main
