-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_convexification_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.convexification_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:11:26.064708+00:00
-- url     : https://prove2.me/theorems/cbc80a71-8e2b-4acd-8a8e-e2f9e20adbfd
-- title:
--   Corollary 5: convexification bound
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   For every device $R$, let $U(R)$ be the smaller of its squashed MI and squashed CMI values, each computed on a complete extension. The lower convex hull is the infimum of $\sum_i p_i U(P_i)$ over all finite normalized ensembles with $\sum_i p_iP_i=P$ at every device input. Complete extensions of the constituent devices are included as representation data. Then
--
--   $$N_{\rm sq}(P)\le\operatorname{LCH}\{\widehat I(A:B),\widehat I(A:B\mid E)\}(P).$$
--
--   The score set is nonempty by the one-term decomposition and bounded below by zero; it is a hull over entire feasible device mixtures, not sampled interpolation.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 55, Corollary 5 / equation (317)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

section Devices

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-- PDF p.55, Corollary 5, (317): the actual lower convex hull bounds Nsq. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem convexification_bound {p : Box X Y A B} (c : CompleteExtension p) :
    squashedNonlocality c ≤ squashedLowerHull p := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
