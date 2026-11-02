-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_amp_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.amp_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:12:17.022197+00:00
-- url     : https://prove2.me/theorems/bc2464ef-09c8-4cf5-9d96-d28f677da9e8
-- title:
--   Unnumbered equation (3): equivalence to the AMP ensemble optimization
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   For a fixed honest input $(x,y)$, define $I_{\rm AMP,(x,y)}(P)$ as the infimum of $I(A:B\downarrow E)$ of the measured ensemble law $p(e)P^e(a,b\mid x,y)$ over every finite non-signaling ensemble that reconstructs $P$ at every input. Then
--
--   $$\max_{x,y}I_{\rm AMP,(x,y)}(P)=N_{\rm sq}(P).$$
--
--   The ensemble constraints remain global even though information is evaluated at a fixed honest setting.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 45, Equation (3) / Appendix XVI A

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

/-- PDF pp.3,45, (3): equality with the AMP ensemble optimization. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem amp_equivalence {p : Box X Y A B} (c : CompleteExtension p) :
    finiteMax (fun xy : X × Y => ampAtInput p xy.1 xy.2) = squashedNonlocality c := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
