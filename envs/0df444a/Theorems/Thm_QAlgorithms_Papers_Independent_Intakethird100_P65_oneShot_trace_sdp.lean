-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_oneShot_trace_sdp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.oneShot_trace_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:42:13.912038+00:00
-- url     : https://prove2.me/theorems/200c3a44-7f8b-4d30-b1f4-dfbe768c2190
-- title:
--   Proposition 3 / Eqs.(17),(18): one-shot cost from an SDP
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For a CPTP channel $\mathcal N:A\to B$ and $\varepsilon\ge0$, let $t_\varepsilon(\mathcal N)$ be the infimum of $\operatorname{Tr}V_B$ over Hermitian $Y,J,V_B$ with $\operatorname{Tr}_B Y\le\varepsilon I_A$, $Y\ge J-J_{\mathcal N}$, $Y\ge0$, $J\ge0$, $\operatorname{Tr}_B J=I_A$, and $J\le I_A\otimes V_B$. Then
--
--   $$S_{\rm NS,\varepsilon}^{(1)}(\mathcal N)=\log_2\left\lceil\sqrt{t_\varepsilon(\mathcal N)}\right\rceil.$$
--
--   The trace infimum is attained by a feasible triple. Integer resource rounding is applied after optimizing the linear objective; the communication cost is its logarithmic postprocessing.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 6, Proposition 3 / Eqs.(17),(18): one-shot cost from an SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Proposition 3, Eqs.(17)--(18), PDF p.6. The trace SDP optimum is attained;
root/ceiling/log are subsequent scalar operations. -/
theorem oneShot_trace_sdp (N : Superop A B) (hN : IsChannel N) (e : ℝ) (he : 0 ≤ e) :
    oneUseSimulationCost .ns N e = roundedTraceCost (traceValue N e) ∧
    ∃ Y J : Mat (A × B), ∃ V : Mat B,
      traceFeasible N e Y J V ∧ V.trace.re = traceValue N e := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
