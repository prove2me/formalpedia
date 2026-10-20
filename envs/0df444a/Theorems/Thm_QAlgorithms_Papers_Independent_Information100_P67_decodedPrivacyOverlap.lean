-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_decodedPrivacyOverlap
-- name    : QAlgorithms.Papers.Independent.Information100.P67.decodedPrivacyOverlap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:51:41.138608+00:00
-- url     : https://prove2.me/theorems/3047c77f-f01d-4a9b-a980-d912f55db351
-- title:
--   Lemma 3.2 (Overlap of decoded privacy tests)
-- statement:
--   Let $K,S,X,C,Y,G_1,G_2$ be distinct positive-dimensional finite tensor factors with $|K|=M\ge1$. Fix the key basis. For $i=1,2$, choose arbitrary unitary diagonal twisting blocks on $ST_i$ and a unitary decoder $D_1:XCG_1\to K_1T_1$ or $D_2:CYG_2\to K_2T_2$, with $|K_i|=M$. Pull each privacy test back through its decoder, retaining its auxiliary factor, and extend by the identity on unused factors to obtain $P,Q$ on $KSXCYG_1G_2$. Then
--
--   $$\|PQ\|_{\rm op}\le\min\{1,|C|/M\}.$$
--
--   The receiver outputs are alternative spaces. The twisting operators can act noncommutatively on the common sender shield. The bound is independent of every shield and auxiliary dimension.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 13, Lemma 3.2 (Overlap of decoded privacy tests)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Lemma 3.2, PDF pp.13–16. Both sender factors are shared; only C is
shared by the receivers. G1,G2 remain distinct full operator factors. -/
theorem decodedPrivacyOverlap [Nonempty S] [Nonempty X] [Nonempty C]
    [Nonempty Y] [Nonempty G1] [Nonempty G2]
    {T1 T2 : Type*} [Fintype T1] [DecidableEq T1] [Nonempty T1]
    [Fintype T2] [DecidableEq T2] [Nonempty T2]
    (M : ℕ) (hM : 0 < M)
    (twist1 : Fin M → Matrix (S × T1) (S × T1) ℂ)
    (twist2 : Fin M → Matrix (S × T2) (S × T2) ℂ)
    (ht1 : ∀ m, twist1 m ∈ Matrix.unitaryGroup (S × T1) ℂ)
    (ht2 : ∀ m, twist2 m ∈ Matrix.unitaryGroup (S × T2) ℂ)
    (D1 : Matrix (Fin M × T1) (X × (C × G1)) ℂ)
    (D2 : Matrix (Fin M × T2) (C × (Y × G2)) ℂ)
    (hD1 : D1ᴴ * D1 = 1 ∧ D1 * D1ᴴ = 1)
    (hD2 : D2ᴴ * D2 = 1 ∧ D2 * D2ᴴ = 1) :
    letI : DecidableEq (Fin M × (S × (X × (C × (Y × (G1 × G2)))))) :=
      Classical.decEq _
    specNorm (n := Fin M × (S × (X × (C × (Y × (G1 × G2))))))
      (firstTest (Y := Y) (G2 := G2) twist1 D1 *
        secondTest (X := X) (G1 := G1) twist2 D2) ≤
      min 1 ((Fintype.card C : ℝ) / M) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
