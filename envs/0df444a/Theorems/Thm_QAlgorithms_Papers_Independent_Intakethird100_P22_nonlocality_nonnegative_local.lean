-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_nonlocality_nonnegative_local
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.nonlocality_nonnegative_local
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:06:39.942191+00:00
-- url     : https://prove2.me/theorems/878f2a15-94ff-4dce-9a79-bea1bfef4870
-- title:
--   Proposition 3: nonnegativity and vanishing on local boxes
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Then
--
--   $$N_{\rm sq}(P)\ge0,\qquad P\text{ admits a local hidden-variable model}\ \Longrightarrow\ N_{\rm sq}(P)=0.$$
--
--   Vanishing on local devices is one-way and asserts no faithfulness converse.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 45, Proposition 3 / equation (219)

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

/-- PDF p.45, Proposition 3, (219): nonnegative and zero on local boxes;
no converse, optimizer, or favorable extension is assumed. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem nonlocality_nonnegative_local {p : Box X Y A B} (c : CompleteExtension p) :
    0 ≤ squashedNonlocality c ∧ (HasLocalModel p → squashedNonlocality c = 0) := by sorry

end Devices

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
