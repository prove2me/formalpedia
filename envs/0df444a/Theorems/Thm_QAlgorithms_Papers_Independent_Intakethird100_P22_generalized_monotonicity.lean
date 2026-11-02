-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P22_generalized_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P22.generalized_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:08:14.931172+00:00
-- url     : https://prove2.me/theorems/c0056825-4009-4f79-8753-01cb7fffd659
-- title:
--   Proposition 6: GMDLOPC monotonicity for the explicit source map
-- statement:
--   All input and output alphabets are finite and nonempty. Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite non-signaling device, and let $\mathcal E(P)$ be its complete extension, with possibly input-dependent pure-member labels. All Shannon information quantities are in bits, with $0\log_2 0=0$. Write $N_{\rm sq}(P)$ for the maximum over honest settings $(x,y)$ of the infimum, over Eve's general measurements, of intrinsic information; intrinsic information itself minimizes classical conditional mutual information over arbitrary stochastic channels on Eve.
--
--   Let $\mu$ on $L$ and $\nu$ on $M$ be independent shared probability laws on finite nonempty alphabets. Let $D_A(x\mid x_o,l)$, $D_B(y\mid y_o,l)$, $R_A(a_o\mid a,x,m)$ and $R_B(b_o\mid b,y,m)$ be normalized local stochastic kernels. Define the source map
--
--   $$P_o(a_o,b_o\mid x_o,y_o)=\sum_{l,m,x,y,a,b}\mu(l)\nu(m)D_A(x\mid x_o,l)D_B(y\mid y_o,l)P(a,b\mid x,y)R_A(a_o\mid a,x,m)R_B(b_o\mid b,y,m).$$
--
--   Then
--
--   $$N_{\rm sq}(P_o)\le N_{\rm sq}(P).$$
--
--   This states monotonicity for the displayed source class of maps.
--
--   Eve retains the dice result $z$ and extension output $e$. Squashed CMI conditions on $(z,e)$; intrinsic-information channels may depend on both. This is the operational convention of XI.B.3 used by the proof, rather than discarding the dice result in display (7).
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, PDF p. 48, Proposition 6 / equations (240)–(245)

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

/-- PDF pp.48–49, Proposition 6, (240): monotonicity for the explicit map.
The apparent max/inf exchange in (260)–(261) is a moderation concern, not a premise. Source convention: Eve keeps the dice
result (p.22, XI.B.3); CE members may depend on (z,e) -/
theorem generalized_monotonicity {X Y A B Xo Yo Ao Bo L M : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype Xo] [Fintype Yo] [Fintype Ao] [Fintype Bo] [Fintype L] [Fintype M]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    [Nonempty Xo] [Nonempty Yo] [Nonempty Ao] [Nonempty Bo] [Nonempty L] [Nonempty M]
    (g : GeneralLocalMap X Y A B Xo Yo Ao Bo L M) (p : Box X Y A B)
    (cp : CompleteExtension p) (co : CompleteExtension (g.apply p)) :
    squashedNonlocality co ≤ squashedNonlocality cp := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P22

end
