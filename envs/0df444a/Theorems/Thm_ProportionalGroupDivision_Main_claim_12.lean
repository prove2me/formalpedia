-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_claim_12
-- name    : ProportionalGroupDivision.Main.claim_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:16.387354+00:00
-- url     : https://prove2.me/theorems/420623ad-6dfa-4457-b96c-85477bf5de1d
-- title:
--   Claim 12 — the residual matrix $B$ of the gifting algorithm is $(\Delta_{p_1},\dots,\Delta_{p_{n_s}})$-structured
-- statement:
--   Throughout, $C'>0$ is a real, $n,n_1,k>0$ are integers with $n\ge n_1\ge n/k$, $A\in[0,1]^{n_s\times m}$ are the valuations of a group with $n_s\le n_1$ agents, and
--
--   $$\Upsilon=\Xi\Big(\frac{n_1k}{n},\frac{n_1k}{n}\Big),\qquad \Xi(s,r)=C\log_2(4s)\sqrt{\log_2(4r)} .$$
--
--   Algorithm 1 is run with removal threshold $C'\Upsilon\sqrt\lambda$ and stopping level $n/k$.
--
--   Let $\Delta_i=\max\{\lambda,n/k\}$ with $\lambda$ taken at the moment agent $i$ is removed from the active set, and $\Delta_i=n/k$ if agent $i$ is never removed; let $p_1,p_2,\dots,p_{n_s}$ be the agents in the order of removal, the never-removed agents last; let $A'$ be $A$ with the gifted columns deleted and $B$ the matrix with rows $A'_{p_1},\dots,A'_{p_{n_s}}$. Then
--
--   $$B\ \text{ is }\ (\Delta_{p_1},\Delta_{p_2},\dots,\Delta_{p_{n_s}})\text{-structured.}$$
--
--   This is the structural half of part (2) of Theorem 10.
--
--   Differences from the source:
--   - generalization: Υ = Ξ(n_1k/n, n_1k/n) with C the constant from Theorem 6 → every constant C > 0 in Ξ; reason: the argument does not use the property of Theorem 6; the statement specializes to the paper's C, which is positive
--   - generalization: Algorithm 1 with arg max and "in any order" left unresolved → every tie-breaking priority τ of goods and agents (a universally quantified parameter); reason: the claim is asserted for every way of resolving the ties, which includes any particular one
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: Algorithm 1 run until it terminates, with a dummy good valued 0 by everyone (p. 12); v ∈ {0,1}^m; Δ_i, p and B as defined on p. 14 → giftRun, the state after n_s + m + 1 rounds of giftStep (every non-final round removes an agent or gifts a new good, so the run has terminated); the dummy good as the value 0 inserted in the maximum defining λ; v the set giftedSet; Δ = giftDelta, p = giftPerm, B = giftResidual with the ungifted goods as column type; reason: the same run and the same constructed objects
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Claim 12 and the definitions of Δ_i, p and B, PDF p. 14 = printed p. 14

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Structured
import Definitions.Def_ProportionalGroupDivision_Main_Gifting

namespace ProportionalGroupDivision.Main

/-- Claim 12 (PDF p. 14): in the setting of Theorem 10, let `Δ_i = max{λ, n/k}` with `λ` at the
moment agent `i` is removed by Algorithm 1 (`Δ_i = n/k` if never removed), let `p_1, …, p_{ns}` be
the removal order (never-removed agents last), and let `B` have rows `A′_{p_1}, …, A′_{p_{ns}}`,
where `A′` is `A` with the gifted columns deleted. Then `B` is `(Δ_{p_1}, …, Δ_{p_{ns}})`-structured. The ties left open by the paper (`arg max`, "in any order") are resolved by an arbitrary priority
`τ`; the claim holds for every `τ`. -/
theorem claim_12 (C C' : ℝ) (hC : 0 < C) (hC' : 0 < C') (n n₁ k : ℕ) (hn : 0 < n)
    (hn₁ : 0 < n₁) (hk : 0 < k) (h₁ : n₁ ≤ n) (h₂ : (n : ℝ) / k ≤ n₁) (ns m : ℕ)
    (hns : ns ≤ n₁) (A : Matrix (Fin ns) (Fin m) ℝ) (hA : ∀ i g, 0 ≤ A i g ∧ A i g ≤ 1)
    (τ : TieOrder ns m) :
    IsStructured
      (giftResidual τ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n)) ((n : ℝ) / k) A)
      (fun ℓ => giftDelta τ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n)) ((n : ℝ) / k) A
        (giftPerm τ (C' * Xi C ((n₁ : ℝ) * k / n) ((n₁ : ℝ) * k / n)) ((n : ℝ) / k) A ℓ)) := by sorry

end ProportionalGroupDivision.Main
