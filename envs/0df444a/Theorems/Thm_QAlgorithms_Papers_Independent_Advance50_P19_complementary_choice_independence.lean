-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_complementary_choice_independence
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.complementary_choice_independence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:58:20.529115+00:00
-- url     : https://prove2.me/theorems/dcd1d1d4-7ee8-4c7b-a865-32ca6849f753
-- title:
--   Degradability is independent of complementary dilation
-- statement:
--   Let $T:\mathcal B(H_A)\to\mathcal B(H_B)$ be a CPTP map between nonzero finite-dimensional Hilbert spaces. Let $V:H_A\to H_B\otimes H_E$ and $W:H_A\to H_B\otimes H_F$ be isometries with the same receiver channel $T$. Define $T_V^c(X)=\operatorname{tr}_{B}(VXV^\dagger)$ and $T_W^c$ analogously. Then
--
--   $$\bigl(\exists D\text{ CPTP}:D\circ T=T_V^c\bigr)\iff\bigl(\exists D'\text{ CPTP}:D'\circ T=T_W^c\bigr).$$
--
--   These equivalent conditions are also equivalent to ordinary degradability of $T$. This permits testing one fixed pure-environment dilation; the degrading maps need not be Gaussian.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 7, Lemma S3

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Lemma S3: fix the receiver channel before BOTH pure dilations.
Existence of an arbitrary CPTP degrading map is independent of that choice,
and agrees with the existential definition of degradability. -/
theorem complementary_choice_independence {A B E F : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype F]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    [Nonempty E] [Nonempty F] (T : Superop A B) (hT : IsChannel T)
    (V : Matrix (B × E) A ℂ) (W : Matrix (B × F) A ℂ)
    (hV : HasReceiverDilation T V) (hW : HasReceiverDilation T W) :
    (Degrades T (complementaryChannel V) ↔ Degrades T (complementaryChannel W)) ∧
      (ChannelDegradable T ↔ Degrades T (complementaryChannel V)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
