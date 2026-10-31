-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P54_skewConfiguration_iff_skewRegion
-- name    : QAlgorithms.Papers.Independent.Intake100.P54.skewConfiguration_iff_skewRegion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:49:21.410061+00:00
-- url     : https://prove2.me/theorems/7266d53e-02ea-4c7d-b1ff-93c07ec9385d
-- title:
--   Proposition 6.4: skew local regions are exactly placed skew shapes
-- statement:
--   Let $\gamma=(\gamma_1\le\cdots\le\gamma_n)\in\mathbb Z^n$ and let $(\gamma,J)$ be a type $A_{n-1}$ local region, meaning that $F^{(\gamma,J)}$ is nonempty. Let $D$ be its associated box configuration, considered up to diagonal slides preserving contents and the orders on equal and adjacent diagonals. Then
--
--   $$D\text{ is a placed skew diagram}\quad\Longleftrightarrow\quad(\gamma,J)\text{ is a skew local region}.$$
--
--   On the left, a skew diagram is a difference of two finite English partition diagrams, with an integer content placement. On the right, every $w\gamma$ for $w\in F^{(\gamma,J)}$ must be calibratable. In type $A$, the numerical conditions in §5.1(c) say that entries one or two positions apart are unequal. The geometric and root-theoretic conditions are defined independently. This result identifies the source's general notion of skewness with classical skew diagrams.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, PDF p. 28, Proposition 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- Proposition 6.4, PDF pp.28–29: geometric recognition as a partition
difference, up to allowed slides, is equivalent to numerical skewness of
the type A local region. Neither direction is built into a data type. -/
theorem skewConfiguration_iff_skewRegion {n : ℕ} (gamma : Fin n → ℤ)
    (hgamma : Monotone gamma) (J : Set (ARoot n))
    (hlocal : (aRegion (fun i => (gamma i : ℝ)) J).Nonempty)
    (D : BoxDrawing n) (hD : ConfigurationFor gamma J D) :
    IsSkewConfiguration D ↔
      IsSkewLocalRegionA (fun i => (gamma i : ℝ)) J := by sorry

end QAlgorithms.Papers.Independent.Intake100.P54

end
