-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_multiway_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.multiway_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:10:10.240193+00:00
-- url     : https://prove2.me/theorems/8fd712f5-a521-484a-9b95-bd9d50fefd6a
-- title:
--   §III, unnumbered extension of (11) to multi-way discussion
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Alice draws a uniform finite message $M$, uses a possibly stochastic encoder to excite $n$ channel uses, and observes $(M,X^n)$. A public forward message $\Phi=\phi(M,X^n)$ is visible to Bob and Eve. Their keys are $K_A=k_A(M,X^n)$ and $K_B=k_B(Y^n,\Phi)$. All design maps are fixed publicly before observations. Message and public alphabets follow the fixed-rate ceiling convention; the key alphabet at rate $R$ has exactly $2^{\lceil nR\rceil}$ labels. A weakly achievable rate $R$ has one sequence of such codes with disagreement tending to zero, $I(K_A;Z^n,\Phi)/n\to0$, and $\liminf H(K_A)/n\ge R$.
--
--   Let $\Lambda:S\to[0,L]$ be bounded and nonnegative, and let $\Gamma>0$ be admissible, meaning that a normalized input law of expected cost at most $\Gamma$ exists. Every operational code obeys $n^{-1}\sum_i\Lambda(S_i)\le\Gamma$ almost surely; each single-letter optimization obeys $\sum_s p(s)\Lambda(s)\le\Gamma$. Excitation and public rates are unrestricted.
--
--   Replace the single forward message by any finite sequence of public messages, each determined by the sender's own observation, private seed and previous transcript. Eve sees the entire transcript. Define weak achievability by the same three conditions and the same almost-sure excitation-cost constraint. Then the interactive capacity satisfies
--   $$C_{\rm SK}^{\rm int}(\Gamma)\le\max_{p:\,\mathbb E\Lambda(S)\le\Gamma} I(X,S;Y\mid Z).$$
--   The maximizing input law exists.
--
--   This extends the upper bound to multi-way discussion without asserting an interactive capacity formula.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 5, §III, unnumbered extension of (11) to multi-way discussion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.5, unnumbered extension of (11): the same attained upper bound
holds for multiple messages. No interactive senderExcitedCapacity equality is asserted. -/
theorem multiway_upper_bound (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : ℝ)
    (hcost : AdmissibleCost cost Gamma) :
    ∃ p : S → ℝ, CostFeasibleInput cost Gamma p ∧
      IsGreatest {v | ∃ q, CostFeasibleInput cost Gamma q ∧ v = upperObjective W q}
        (upperObjective W p) ∧
      interactiveCapacity W cost Gamma ≤ (upperObjective W p : EReal) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
