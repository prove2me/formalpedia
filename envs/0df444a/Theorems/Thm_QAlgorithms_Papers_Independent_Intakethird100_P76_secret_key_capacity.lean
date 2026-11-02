-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_secret_key_capacity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.secret_key_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:07:35.601323+00:00
-- url     : https://prove2.me/theorems/a760c51e-37e2-4156-8460-c900567fda3c
-- title:
--   Proposition 1 (Secret Key Capacity); precise result selected for the p.1 paper seed
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Alice draws a uniform finite message $M$, uses a possibly stochastic encoder to excite $n$ channel uses, and observes $(M,X^n)$. A public forward message $\Phi=\phi(M,X^n)$ is visible to Bob and Eve. Their keys are $K_A=k_A(M,X^n)$ and $K_B=k_B(Y^n,\Phi)$. All design maps are fixed publicly before observations. Message and public alphabets follow the fixed-rate ceiling convention; the key alphabet at rate $R$ has exactly $2^{\lceil nR\rceil}$ labels. A weakly achievable rate $R$ has one sequence of such codes with disagreement tending to zero, $I(K_A;Z^n,\Phi)/n\to0$, and $\liminf H(K_A)/n\ge R$.
--
--   Let $\Lambda:S\to[0,L]$ be bounded and nonnegative, and let $\Gamma>0$ be admissible, meaning that a normalized input law of expected cost at most $\Gamma$ exists. Every operational code obeys $n^{-1}\sum_i\Lambda(S_i)\le\Gamma$ almost surely; each single-letter optimization obeys $\sum_s p(s)\Lambda(s)\le\Gamma$. Excitation and public rates are unrestricted.
--
--   The operational forward secret-key capacity equals an attained auxiliary maximum:
--   $$C_{\rm SK}(\Gamma)=\max_{p(s),p(u\mid x,s),p(w\mid u)}\{I(U;Y\mid W)-I(U;Z\mid W)\}.$$
--   Every auxiliary law is constructed as $p(w\mid u)p(u\mid x,s)p(s)W(x,y,z\mid s)$, and the input obeys the expected-cost constraint. The maximum ranges over finite nonempty auxiliary alphabets.
--
--   This identifies the operational capacity without defining it by the proposed information formula.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 4, Proposition 1 (Secret Key Capacity); precise result selected for the p.1 paper seed

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

/-- PDF p.4, Proposition 1, (8), with factorization (10) and attained maximum. -/
theorem secret_key_capacity (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : ℝ)
    (hcost : AdmissibleCost cost Gamma) :
    ∃ u w : ℕ, 0 < u ∧ 0 < w ∧ ∃ A : Aux S X u w,
      CostFeasibleInput cost Gamma A.input ∧
      IsGreatest (auxValues W cost Gamma) (auxObjective W A) ∧
      senderExcitedCapacity W cost (some Gamma) = (auxObjective W A : EReal) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
