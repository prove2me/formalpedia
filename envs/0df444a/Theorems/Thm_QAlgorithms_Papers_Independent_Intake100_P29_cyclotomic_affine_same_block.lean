-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P29_cyclotomic_affine_same_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P29.cyclotomic_affine_same_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:29:21.747991+00:00
-- url     : https://prove2.me/theorems/414ff609-6ce6-449a-9cf1-5cfd73d1dd00
-- title:
--   Cyclotomic and affine block membership coincide
-- statement:
--   Let $F$ be an algebraically closed field, $n,r\ge1$, $q\in F^\times\setminus\{1\}$, and $Q=(Q_1,\ldots,Q_r)\in(F^\times)^r$, with repeated parameters allowed. Let $\mathcal H_n^{\mathrm{aff}}$ be the extended affine Hecke algebra and put $H=\mathcal H_n^{\mathrm{aff}}/\langle\prod_{a=1}^r(X_1-Q_a)\rangle$. For nonzero simple finite-dimensional right $H$-modules $D,D'$, inflated to affine modules through this quotient,
--
--   $$
--   D\text{ and }D'\text{ lie in the same }H\text{-block}
--   \quad\Longleftrightarrow\quad
--   D\text{ and }D'\text{ lie in the same }\mathcal H_n^{\mathrm{aff}}\text{-block}.
--   $$
--
--   Blocks mean finite linkage by nonsplit extensions between simple modules, in either direction. On the affine side, intermediate simple modules need not factor through $H$. This identifies the quotient's block relation with the restriction of affine block linkage.
--
--   **Formalization Note** Matrices act on row vectors on the right. Positive ranks are written as successors. Module isomorphisms identify coordinate representatives, and quotient modules are exactly representations annihilated by the cyclotomic polynomial.
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, PDF p. 1, Theorem A

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

variable {F : Type} [Field F]

/-- Theorem A, PDF p. 1. Ranks m+1 and r+1 encode n,r≥1 exactly.
Affine linkage on the right may pass through arbitrary simple affine modules. -/
theorem cyclotomic_affine_same_block [IsAlgClosed F] (m r : ℕ)
    (q : F) (hq : q ≠ 0) (hqOne : q ≠ 1) (Q : Fin (r + 1) → F) (hQ : ∀ a, Q a ≠ 0)
    (D Dprime : AffineModule F m q) (hD : Simple D) (hDprime : Simple Dprime)
    (hDQ : FactorsCyclotomic Q D) (hDprimeQ : FactorsCyclotomic Q Dprime) :
    Linkage (FactorsCyclotomic Q) (FactorsCyclotomic Q) D Dprime ↔
      Linkage (fun _ => True) (fun _ => True) D Dprime := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P29
