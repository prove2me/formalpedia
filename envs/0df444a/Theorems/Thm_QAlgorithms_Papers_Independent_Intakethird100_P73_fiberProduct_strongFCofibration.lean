-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P73_fiberProduct_strongFCofibration
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P73.fiberProduct_strongFCofibration
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:02:18.220255+00:00
-- url     : https://prove2.me/theorems/618e59f1-9038-4adb-ac69-dfe95a8503a2
-- title:
--   Lemma 24: fiberwise products of strong cofibrations
-- statement:
--   Let $B$ be a weakly Hausdorff k-space. Let $i_1:A_1\to X$ and $i_2:A_2\to Y$ be strong $\bar f$-cofibrations in $\mathcal K/B$, where all four spaces are k-spaces over $B$ and all maps commute with their projections. A strong $\bar f$-cofibration has the left lifting property against every map over $B$ that is both a fiberwise homotopy equivalence and a fiberwise covering-homotopy fibration. Then
--
--   $$
--   i_1\times_B i_2:A_1\times_B A_2\longrightarrow X\times_B Y
--   \quad\text{is a strong }\bar f\text{-cofibration}.
--   $$
--
--   The displayed map sends $(a_1,a_2)$ to $(i_1(a_1),i_2(a_2))$. Each fiber product is formed with the kification of the subspace topology on the equal-base pairs. No separation assumption on the total spaces is imposed.
--
--   This gives stability of strong fiberwise cofibrations under products over the fixed base.
-- source:
--   Simplicial principal bundles in parametrized spaces, arXiv:1203.2460v4, PDF p. 20, Lemma 24

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P73

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P73

open CategoryTheory

open scoped Topology

/-- Roberts--Stevenson, Lemma 24, arXiv:1203.2460v4, PDF p. 20.
The fiberwise product of two strong fbar-cofibrations is a strong
fbar-cofibration. All objects are k-spaces over a weakly Hausdorff k-space B. -/
theorem fiberProduct_strongFCofibration
    (B : KSpace) (hB : IsWeaklyHausdorff B)
    (A X D Y : SpaceOver B) (i : MapOver A X) (j : MapOver D Y)
    (hi : IsStrongFCofibration i) (hj : IsStrongFCofibration j) :
    IsStrongFCofibration (fiberProductMap i j) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P73

end
