-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_quadratic_success
-- name    : QAlgorithms.Papers.Independent.Support50.P19.quadratic_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:40:44.528707+00:00
-- url     : https://prove2.me/theorems/71028781-9dd8-462a-9938-5e0912d92cc1
-- title:
--   Quadratic near-capacity success exponent
-- statement:
--   For each entanglement-breaking channel $\mathcal N$ on nonzero finite complex spaces, choose an attained ordinary-radius center $\sigma_*$ and a uniform finite $c>1$ as in the near-one estimate, before all rates and codes. Put $L=\log_2c$ and $\Delta=R-\chi(\mathcal N)$. For every $R$ with $\Delta>0$, $\Delta/(8L^2)\le1$, and $\Delta/(8L^2)<\log_2 3/(4L)$, any $n\ge1$ use code with actual rate at least $R$ satisfies
--   $$p_{\rm succ}\le2^{-n\Delta^2/(32L^2)}.$$
--   Message numbers are positive integers and success is the uniform average with unrestricted mixed block encodings. These small-gap conditions ensure the chosen $\alpha=1+\Delta/(8L^2)$ lies in the valid range. This gives an explicit exponential rate of decay near capacity.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 23, eq24

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

/-- PDF p.23, (24): the near-capacity quadratic exponent, with a strict cap from (20).
The intermediate printed display omits factor 4; its subsequent chain and chosen alpha
use chi + 4(alpha-1)L^2 ≤ (R+chi)/2. We retain that corrected reading. -/
theorem quadratic_success [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N) :
    ∃ sigma : Matrix J J ℂ, ∃ c : ℝ, CenterControl N sigma c ∧
      ∀ R : ℝ, (QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N) < R →
        (R - (QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N)) / (8 * (Real.logb 2 c) ^ 2) ≤ 1 →
        (R - (QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N)) / (8 * (Real.logb 2 c) ^ 2) < Real.logb 2 3 / (4 * Real.logb 2 c) →
        ∀ n : ℕ, 0 < n → ∀ M : ℕ, 0 < M → R ≤ (Real.logb 2 (M : ℝ) / (n : ℝ)) →
          ∀ C : UACode (Fin n → I) (Fin n → J) M,
            uaCodeSuccess (channelPower N n) C ≤
              (2 : ℝ) ^ (-((n : ℝ) * (R - (QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N)) ^ 2 / (32 * (Real.logb 2 c) ^ 2))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
