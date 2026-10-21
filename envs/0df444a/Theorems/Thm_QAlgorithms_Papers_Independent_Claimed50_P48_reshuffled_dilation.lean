-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_reshuffled_dilation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.reshuffled_dilation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:56:26.550101+00:00
-- url     : https://prove2.me/theorems/bbe761c5-f2d8-4d3a-ab66-77fe67eb6ae8
-- title:
--   Reshuffled Stinespring representation of arbitrary CP maps
-- statement:
--   For an arbitrary finite linear $V:H_A\to H_B\otimes H_C$, with $H_A\ne0$, define the reshuffled matrix by $S_{c,(a,b)}=V_{(b,c),a}$. Then for every operator $X$,
--
--   $$\operatorname{Tr}_B(VXV^*)=S(X\otimes I_B)S^*,\qquad
--   \operatorname{Tr}_B(S^*S)=V^*V.$$
--
--   In particular, the last expression is $I_A$ when $V$ is isometric. For all vectors $a,b,c$ the construction also gives $\langle\overline b\otimes c|V|a\rangle=\langle c|S|a\otimes b\rangle$, where conjugation uses the chosen $B$ basis. This is the general operator reshuffling behind the preceding complementary-channel formulas.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 9, Reshuffled Stinespring representation of arbitrary CP maps

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.9: computed reshuffling of arbitrary V. Tr_B(S*S)=V*V;
only trace-preserving dilations make it I. -/
theorem reshuffled_dilation [Nonempty A] (V : Matrix (B × C) A ℂ) :
    (∀ rho, complementaryChannel V rho = dilationReshuffle V * (rho ⊗ₖ (1 : Matrix B B ℂ)) * (dilationReshuffle V)ᴴ) ∧
    traceRight ((dilationReshuffle V)ᴴ * dilationReshuffle V) = Vᴴ * V ∧
    (Vᴴ * V = 1 → traceRight ((dilationReshuffle V)ᴴ * dilationReshuffle V) = 1) ∧
    (∀ (a : A → ℂ) (b : B → ℂ) (c : C → ℂ),
      (∑ j, ∑ k, conj (conj (b j) * c k) * (∑ i, V (j,k) i * a i)) =
        ∑ k, conj (c k) * (∑ i, ∑ j, dilationReshuffle V k (i,j) * (a i * b j))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
