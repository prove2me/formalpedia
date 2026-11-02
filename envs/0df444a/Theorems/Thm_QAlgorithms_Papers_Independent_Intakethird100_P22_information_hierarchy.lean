-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_information_hierarchy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.information_hierarchy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:10:01.250393+00:00
-- url     : https://prove2.me/theorems/80e2b5f0-419f-4099-848d-74df046d0918
-- title:
--   Observation 2: hierarchy with MI and CMI
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Write $\widehat I(A:B)$ and $\widehat I(A:B\mid E)$ for squashing classical mutual information and conditional mutual information, respectively, on the same complete extension and in the same max-then-inf order. Then both comparisons hold:
--
--   $$N_{\rm sq}(P)\le\widehat I(A:B),\qquad N_{\rm sq}(P)\le\widehat I(A:B\mid E).$$
--
--   Each is an upper bound on the source-defined squashed intrinsic information.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 54, Observation 2 / equations (311), (312)

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

/-- PDF p.54, Observation 2, (311),(312): both hierarchy comparisons. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem information_hierarchy {p : Box X Y A B} (c : CompleteExtension p) :
    squashedNonlocality c ≤ squashedMI c ∧ squashedNonlocality c ≤ squashedCMI c := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
