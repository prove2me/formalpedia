-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P36_erasureHolevoAdditivity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P36.erasureHolevoAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:17:14.657627+00:00
-- url     : https://prove2.me/theorems/1743f94f-e7fe-4cea-9a63-a1849fa1007b
-- title:
--   Holevo additivity with arbitrarily many erasure factors
-- statement:
--   Let $\mathcal N$ be any quantum channel between nonzero finite-dimensional registers. For an integer $d\ge1$, a probability $p\in[0,1]$, and any integer $n\ge0$, let $\mathcal E_{p,d}$ be the pure orthogonal-flag erasure channel. Then
--
--   $$
--   C^{(1)}(\mathcal N\otimes\mathcal E_{p,d}^{\otimes n})=C^{(1)}(\mathcal N)+nC^{(1)}(\mathcal E_{p,d}).
--   $$
--
--   Here $C^{(1)}$ is unregularized Holevo information, optimized over every normalized finite ensemble of mixed input states. The joint inputs may be entangled across $\mathcal N$ and all erasure factors. At $n=0$ the erasure tensor factor is the one-dimensional identity.
--
--   Thus independent erasure factors add their individual Holevo information even in the presence of an arbitrary partner channel.
-- source:
--   Superadditivity of private information for any number of uses of the channel, arXiv:1502.05326v1, PDF p. 3, Lemma 3, (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P36

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory

-- These imports are pinned accepted libraries, permitted by the repair task.
-- P08.Ensemble allows an impossible zero-sized normalized ensemble; its total=1
-- field excludes that case without a separate positive-size field.

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel maximumCoherentInformation dilationPower erasureDilation)

open QAlgorithms.Papers.Independent.Dependency50.P07 (accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P48 (privateMaximum)

variable {A B E C D : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D]

/-- Lemma 3, PDF p.3 (18): unregularized Holevo information is additive
with arbitrary many pure-flag erasure factors and arbitrary entangled inputs.
The full probability interval is allowed; n=0 is the scalar identity. -/
theorem erasureHolevoAdditivity [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (d : ℕ) (hd : 0 < d)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelHolevo (tensorChannel N (piSuperop (fun _ : Fin n => erasureReceiver p d))) =
      channelHolevo N + (n : ℝ) * channelHolevo (erasureReceiver p d) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P36

end
