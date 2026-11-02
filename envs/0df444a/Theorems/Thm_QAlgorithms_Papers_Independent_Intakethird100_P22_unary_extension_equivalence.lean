-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_unary_extension_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.unary_extension_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:13:01.108969+00:00
-- url     : https://prove2.me/theorems/8d222845-6800-4c05-81a1-708f7329236e
-- title:
--   Unnumbered equation (216): optimization over unary-input extensions
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Let $\widetilde P(a,b,e\mid x,y)$ range over all finite-output, fully tripartite non-signaling extensions of $P$ with unary Eve input. The extension constraints include input-independent Eve marginal and the no-signaling equalities conditional on each Eve output. Then
--
--   $$N_{\rm sq}(P)=\max_{x,y}\inf_{\widetilde P:\,\sum_e\widetilde P=P} I(A:B\mid E)_{\widetilde P(\cdot\mid x,y)}.$$
--
--   No minimizing extension is assumed to exist, and the CE generation property is not built into the definition of complete extension.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 44, Equation (216)

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

/-- PDF pp.44–45, (216): CE squashing equals optimization over all unary extensions.
The cited generation result remains theorem content, never a CE field. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem unary_extension_equivalence {p : Box X Y A B} (c : CompleteExtension p) :
    squashedNonlocality c = extensionForm p := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
