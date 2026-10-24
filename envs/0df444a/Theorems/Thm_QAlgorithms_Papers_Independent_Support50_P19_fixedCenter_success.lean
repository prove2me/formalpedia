-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_fixedCenter_success
-- name    : QAlgorithms.Papers.Independent.Support50.P19.fixedCenter_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:43:15.880192+00:00
-- url     : https://prove2.me/theorems/cbd01b04-fc23-4180-beb7-c27e5b82856a
-- title:
--   Success bound about an arbitrary fixed center
-- statement:
--   Let $\mathcal N:A\to B$ be a channel on nonzero finite complex spaces, $1<\alpha\le2$, and let $\sigma$ be any density operator on $B$. A uniform-message code of $M\ge1$ messages using $n\ge1$ channel uses has actual rate $R=\log_2M/n$ and average success satisfying
--   $$p_{\rm succ}\le2^{-n\frac{\alpha-1}{\alpha}\left(R-\frac1n\widetilde K_\alpha^{[\sigma^{\otimes n}]}(\mathcal N^{\otimes n})\right)},\qquad\widetilde K_\alpha^{[\tau]}(\mathcal M)=\max_\rho\widetilde D_\alpha(\mathcal M(\rho)\Vert\tau).$$
--   Input density operators and block encodings are unrestricted. If the fixed-center radius is infinite, the right side is $+\infty$, rather than an exponential computed from a totalized zero. This isolates the center-dependent quantity used in the Hadamard argument.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 25, fixedCenterBound

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

/-- PDF p.25, (26): arbitrary output center; infinite fixed-center radii stay infinite. -/
theorem fixedCenter_success [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (sigma : {X : Matrix J J ℂ // IsDensityMatrix X})
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (C : UACode (Fin n → I) (Fin n → J) M) :
    ENNReal.ofReal (uaCodeSuccess (channelPower N n) C) ≤
      codingBound n a ((Real.logb 2 (M : ℝ) / (n : ℝ)))
        (((1 / (n : ℝ) : ℝ) : EReal) *
          fixedRadius true a (channelPower N n) (tensorPower n sigma.1)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
