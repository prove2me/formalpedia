-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_sqrt_success
-- name    : QAlgorithms.Papers.Independent.Support50.P19.sqrt_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:41:44.091992+00:00
-- url     : https://prove2.me/theorems/61450d12-63b1-4a56-b0ed-06426ab81e22
-- title:
--   Eventual square-root-block success bound
-- statement:
--   For every entanglement-breaking channel $\mathcal N$ on nonzero finite complex spaces, there exist an attained ordinary-radius center $\sigma_*$, a uniform $c>1$, and $n_0\ge1$, chosen before blocklength, rate, and code, such that $1/\sqrt n\le1$ and $1/\sqrt n<\log_2 3/(4\log_2c)$ for every $n\ge n_0$. For every $R>\chi(\mathcal N)$, any such $n$-use code of actual rate at least $R$ satisfies
--   $$p_{\rm succ}\le2^{-\frac{\sqrt n}{1+1/\sqrt n}\left(R-\left[\chi(\mathcal N)+\frac4{\sqrt n}(\log_2c)^2\right]\right)}.$$
--   Success is the uniform average, with arbitrary mixed joint codewords. This eventual alternative uses $\alpha=1+1/\sqrt n$; its decay is exponential in $\sqrt n$.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 23, sqrtBlockBound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF p.23: the alternative sqrt(n) exponent is eventual, so alpha=1+1/sqrt(n)
lies in (20). This is not the exponential-in-n strong converse itself. -/
theorem sqrt_success [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N) :
    ∃ sigma : Matrix J J ℂ, ∃ c : ℝ, CenterControl N sigma c ∧
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
        1 / Real.sqrt (n : ℝ) < Real.logb 2 3 / (4 * Real.logb 2 c) ∧
        1 / Real.sqrt (n : ℝ) ≤ 1 ∧
        ∀ R : ℝ, (QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N) < R → ∀ M : ℕ, 0 < M → R ≤ (Real.logb 2 (M : ℝ) / (n : ℝ)) →
          ∀ C : UACode (Fin n → I) (Fin n → J) M,
            uaCodeSuccess (channelPower N n) C ≤
              (2 : ℝ) ^ (-(Real.sqrt (n : ℝ) / (1 + 1 / Real.sqrt (n : ℝ))) *
                (R - ((QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N) + 4 / Real.sqrt (n : ℝ) * (Real.logb 2 c) ^ 2))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
