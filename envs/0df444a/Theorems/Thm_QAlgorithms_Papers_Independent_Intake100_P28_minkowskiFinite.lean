-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_minkowskiFinite
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.minkowskiFinite
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:27:51.211479+00:00
-- url     : https://prove2.me/theorems/779104c2-c7a8-40e6-9cf7-77068786d158
-- title:
--   Theorem 1.3, explicit finite-dimensional case
-- statement:
--   Let $H_1,H_2,H_3$ be nonzero finite-dimensional complex Hilbert spaces, let $A\ge0$ on their tensor product, and let $p,q>0$. Write $\operatorname{Tr}_j$ for the unnormalized partial trace that removes factor $j$. Define
--   $$
--   L_{p,q}(A)=\operatorname{Tr}_3\left(\operatorname{Tr}_2[(\operatorname{Tr}_1 A^q)^{p/q}]\right)^{q/p},\qquad
--   R_{p,q}(A)=\operatorname{Tr}_3\operatorname{Tr}_1[(\operatorname{Tr}_2 A^p)^{q/p}].
--   $$
--   Then
--   $$
--   1\le q\le p\le2\ \Longrightarrow\ L_{p,q}(A)\le R_{p,q}(A),\qquad
--   0<p\le1,\ q\ge p\ \Longrightarrow\ R_{p,q}(A)\le L_{p,q}(A).
--   $$
--   There is no final scalar root. The $q/p$ power on the left is taken before the last trace.
--
--   This is the explicitly finite-dimensional part of Theorem 1.3. The unrestricted separable-space assertion and its zero endpoint are separately deferred.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 4, Theorem 1.3, explicit finite-dimensional case

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1.3, PDF p.4: explicitly finite-dimensional part; positive parameters.
The full separable claim and the undefined p=0 endpoint are deferred. -/
theorem minkowskiFinite {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (A : Mat (Fin a × (Fin b × Fin c))) (hA : A.PosSemidef) :
    (1 ≤ q → q ≤ p → p ≤ 2 → minkowskiLeft p q A ≤ minkowskiRight p q A) ∧
    (p ≤ 1 → p ≤ q → minkowskiRight p q A ≤ minkowskiLeft p q A) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
