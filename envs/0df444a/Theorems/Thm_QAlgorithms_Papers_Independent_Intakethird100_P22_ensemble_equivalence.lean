-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_ensemble_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.ensemble_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:13:41.125021+00:00
-- url     : https://prove2.me/theorems/8810e5f9-f13f-4cd3-a0c7-e378ebc1aea9
-- title:
--   Unnumbered equation (218): ensemble convex-roof form
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Let $\{p_i,P_i\}$ range over all finite ensembles of non-signaling devices in the same polytope, with nonnegative normalized weights and $\sum_i p_iP_i(a,b\mid x,y)=P(a,b\mid x,y)$ for every input and output. Then
--
--   $$N_{\rm sq}(P)=\max_{x,y}\inf_{\{p_i,P_i\}}\sum_i p_i I(A:B)_{P_i(\cdot\mid x,y)}.$$
--
--   The ensemble members need not be extreme, and the infimum precedes the final honest-input maximum.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 45, Equation (218)

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

/-- PDF p.45, (218): all-device ensemble convex-roof form; no inf/max exchange. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem ensemble_equivalence {p : Box X Y A B} (c : CompleteExtension p) :
    squashedNonlocality c = ensembleForm p := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
