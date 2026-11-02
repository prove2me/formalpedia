-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_auxiliary_cardinalities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.auxiliary_cardinalities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:08:23.817955+00:00
-- url     : https://prove2.me/theorems/b807d98d-2ef6-4932-867a-fd18bfeaa41a
-- title:
--   §III, unnumbered auxiliary-cardinality bounds
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Alice draws a uniform finite message $M$, uses a possibly stochastic encoder to excite $n$ channel uses, and observes $(M,X^n)$. A public forward message $\Phi=\phi(M,X^n)$ is visible to Bob and Eve. Their keys are $K_A=k_A(M,X^n)$ and $K_B=k_B(Y^n,\Phi)$. All design maps are fixed publicly before observations. Message and public alphabets follow the fixed-rate ceiling convention; the key alphabet at rate $R$ has exactly $2^{\lceil nR\rceil}$ labels. A weakly achievable rate $R$ has one sequence of such codes with disagreement tending to zero, $I(K_A;Z^n,\Phi)/n\to0$, and $\liminf H(K_A)/n\ge R$.
--
--   Let $\Lambda:S\to[0,L]$ be bounded and nonnegative, and let $\Gamma>0$ be admissible, meaning that a normalized input law of expected cost at most $\Gamma$ exists. Every operational code obeys $n^{-1}\sum_i\Lambda(S_i)\le\Gamma$ almost surely; each single-letter optimization obeys $\sum_s p(s)\Lambda(s)\le\Gamma$. Excitation and public rates are unrestricted.
--
--   The unrestricted auxiliary maximum in Proposition 1 is attained with
--   $$|\mathcal W|\le |X||S|+3,\qquad |\mathcal U|\le (|X||S|+3)(|X||S|+1).$$
--   The maximizer obeys the fixed-channel factorization and the expected-cost constraint.
--
--   These bounds reduce the auxiliary optimization to bounded finite alphabets.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 4, §III, unnumbered auxiliary-cardinality bounds

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

/-- PDF p.4: bounded auxiliaries attain the unrestricted maximum. -/
theorem auxiliary_cardinalities (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : ℝ)
    (hcost : AdmissibleCost cost Gamma) :
    ∃ u w : ℕ, 0 < u ∧ 0 < w ∧ w ≤ Fintype.card X * Fintype.card S + 3 ∧
      u ≤ (Fintype.card X * Fintype.card S + 3) *
        (Fintype.card X * Fintype.card S + 1) ∧
      ∃ A : Aux S X u w, CostFeasibleInput cost Gamma A.input ∧
        IsGreatest (auxValues W cost Gamma) (auxObjective W A) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
