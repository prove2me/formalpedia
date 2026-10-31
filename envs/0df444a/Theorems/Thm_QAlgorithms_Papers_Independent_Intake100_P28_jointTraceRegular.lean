-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_jointTraceRegular
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.jointTraceRegular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:33:35.122613+00:00
-- url     : https://prove2.me/theorems/ab3b5c50-c09f-41b0-819d-eb71cc40d352
-- title:
--   Lemma 2.6: regular convexity and full stated concavity
-- statement:
--   Let $n\ge1$ and let $B$ be any fixed complex $n\times n$ matrix. For spectral powers define
--   $$
--   J_{p,r}^{B}(A,X)=\operatorname{Tr}\bigl[A^{p/2}B^*X^{1-r}BA^{p/2}\bigr].
--   $$
--   If $1\le r\le p\le2$, then $J$ is jointly convex on $A\ge0,X>0$. If $0<p<r<1$, then $J$ is jointly concave on $A,X\ge0$:
--   $$
--   J(tA_0+(1-t)A_1,tX_0+(1-t)X_1)
--   \le tJ(A_0,X_0)+(1-t)J(A_1,X_1)
--   $$
--   in the convex range, with the reverse inequality in the concave range, for every $t\in[0,1]$.
--
--   This is the regular convex content and the exact strict concavity range of Lemma 2.6.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 10, Lemma 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.6, PDF pp.9–10: strict 0<p<r<1 concavity; regular convex branch. -/
theorem jointTraceRegular {n : ℕ} (hn : 0 < n) (p r : ℝ) (B : Mat (Fin n)) :
    (1 ≤ r → r ≤ p → p ≤ 2 →
      ConvexOn ℝ (regularPairs (Fin n)) (jointTrace p r B)) ∧
    (0 < p → p < r → r < 1 →
      ConcaveOn ℝ (psdPairs (Fin n)) (jointTrace p r B)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
