-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_disjointPrivacyOverlap
-- name    : QAlgorithms.Papers.Independent.Information100.P67.disjointPrivacyOverlap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:52:44.353462+00:00
-- url     : https://prove2.me/theorems/56704748-c892-47cc-a971-4c89fba3383c
-- title:
--   Unnumbered main ingredient: exact disjoint-receiver overlap (3.31)
-- statement:
--   Under the decoded-test assumptions of Lemma 3.2, suppose the common receiver factor $C$ is one dimensional. The receivers $XG_1$ and $YG_2$ then have disjoint supports, while both tests retain the same sender key and shield. For every $M\ge1$ and all positive-dimensional shields and receiver factors,
--
--   $$\|PQ\|_{\rm op}=1/M.$$
--
--   This exact overlap is stronger than an upper bound and does not require the twisting blocks on the common sender shield to commute.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 4, Unnumbered main ingredient: exact disjoint-receiver overlap (3.31)

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

/-- Exact disjoint-receiver overlap (3.31), PDF pp.14–15.
Dimension-one common receiver and arbitrary shared sender shield. -/
theorem disjointPrivacyOverlap [Nonempty S] [Nonempty X] [Nonempty C]
    [Nonempty Y] [Nonempty G1] [Nonempty G2]
    {T1 T2 : Type*} [Fintype T1] [DecidableEq T1] [Nonempty T1]
    [Fintype T2] [DecidableEq T2] [Nonempty T2]
    (hC : Fintype.card C = 1) (M : ℕ) (hM : 0 < M)
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
        secondTest (X := X) (G1 := G1) twist2 D2) = (M : ℝ)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
