-- Prove2me | Theorems.Thm_UnderstandingML_vcDim_linearCombClass_le
-- name    : UnderstandingML.vcDim_linearCombClass_le
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:00:51.705876+00:00
-- url     : https://prove2.me/theorems/13962c31-8eb7-4cce-9880-1507d0ac0c38
-- title:
--   Lemma 10.3: for T ≥ 3 and VCdim(B) ≥ 3, VCdim(L(B, T)) ≤ T(VCdim(B) + 1)(3 log(T(VCdim(B) + 1)) + 2)
-- statement:
--   **Lemma 10.3.** Let $B$ be a base class and let $L(B,T)$ be as defined in Equation (10.4). Assume that both $T$ and $\mathrm{VCdim}(B)$ are at least $3$. Then
--   $$\mathrm{VCdim}(L(B,T)) \le T(\mathrm{VCdim}(B) + 1)\big(3\log(T(\mathrm{VCdim}(B) + 1)) + 2\big).$$
--
--   Formally: with $\mathrm{VCdim}(B) = d \ge 3$ and $T \ge 3$, `vcDim (linearCombClass B T)` is at most the integer part of the right-hand side (natural logarithm).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.3.1 p. 139, Lemma 10.3 with its proof (via Sauer's lemma, Theorem 9.2 and Lemma A.1)

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 10.3** (p. 139). Let `B` be a base class and let `L(B, T)` be as defined in Equation
(10.4). Assume that both `T` and `VCdim(B)` are at least `3`. Then
`VCdim(L(B, T)) ≤ T (VCdim(B) + 1)(3 log(T (VCdim(B) + 1)) + 2)` (natural logarithm; the
right-hand side is real, and the VC-dimension is at most its integer part). -/
theorem vcDim_linearCombClass_le {X : Type*} (B : Set (X → Bool)) (T d : ℕ) (hT : 3 ≤ T)
    (hd : 3 ≤ d) (hB : vcDim B = d) :
    vcDim (linearCombClass B T) ≤
      (⌊(T * (d + 1) : ℝ) * (3 * Real.log (T * (d + 1)) + 2)⌋₊ : ℕ∞) := by sorry

end UnderstandingML
