-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_nonlocality_convex
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.nonlocality_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:07:32.637764+00:00
-- url     : https://prove2.me/theorems/19b702df-e8dc-4aeb-9258-8559fa9c45be
-- title:
--   Proposition 4: convexity
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   For two devices $P,Q$ in the same fixed polytope and every $\lambda\in[0,1]$, with the mixture computed pointwise,
--
--   $$N_{\rm sq}(\lambda P+(1-\lambda)Q)\le\lambda N_{\rm sq}(P)+(1-\lambda)N_{\rm sq}(Q).$$
--
--   The claim holds for arbitrary complete extensions of each indicated device and includes both endpoints.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 46, Proposition 4 / equation (222)

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

/-- PDF p.46, Proposition 4, (222): convexity, including both endpoints.
The CE arguments are arbitrary complete extensions of the specified devices. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem nonlocality_convex (p q : Box X Y A B) (t : ℝ) (ht : 0 ≤ t) (htOne : t ≤ 1)
    (cp : CompleteExtension p) (cq : CompleteExtension q)
    (cm : CompleteExtension (correlationMixture p q t)) :
    squashedNonlocality cm ≤ t * squashedNonlocality cp + (1-t) * squashedNonlocality cq := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
