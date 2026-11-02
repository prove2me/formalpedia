-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_nonlocality_subextensive
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.nonlocality_subextensive
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:08:55.085041+00:00
-- url     : https://prove2.me/theorems/c2f32240-e19b-4ae1-801a-003d127671df
-- title:
--   Proposition 8: support-sensitive subextensivity
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Let $d_A=\max_x|\{a:P_A(a\mid x)>0\}|$ and $d_B=\max_y|\{b:P_B(b\mid y)>0\}|$ be the maximum support sizes of the computed no-signaling marginals. Then
--
--   $$N_{\rm sq}(P)\le\log_2\min\{d_A,d_B\}.$$
--
--   Both support sizes are at least one. Reference inputs used to compute the marginals are arbitrary and do not affect their values.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 52, Proposition 8 / equation (293)

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

/-- PDF p.52, Proposition 8, (293): support dimensions, not ambient cardinalities.
Normalization and nonempty inputs imply both log arguments are at least one. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem nonlocality_subextensive {p : Box X Y A B} (c : CompleteExtension p) (x : X) (y : Y) :
    squashedNonlocality c ≤ Real.logb 2 (min (aliceSupport p y) (bobSupport p x) : ℕ) := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
