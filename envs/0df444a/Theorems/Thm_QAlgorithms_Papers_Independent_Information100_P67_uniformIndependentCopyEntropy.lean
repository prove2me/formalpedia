-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_uniformIndependentCopyEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P67.uniformIndependentCopyEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:59:58.230424+00:00
-- url     : https://prove2.me/theorems/fa31de0a-0f43-489a-8a40-8b2bbfcddb6f
-- title:
--   Unnumbered Appendix B.3 result: dimension-uniform independent-copy estimate (6.15)
-- statement:
--   For every normalized density matrix $\theta_{FE'}$ on finite nonempty systems, every integer $n\ge1$, and every $0<v<1$, let $c_F=8\log_2(2\dim F+1)$. Then
--
--   $$H_{\max}^{v}(F^n|E'^{n})_{\theta^{\otimes n}}\le nH(F|E')_\theta+c_F\sqrt{n\log_2(2/v^2)}.$$
--
--   The smooth max-entropy uses subnormalized purified-distance smoothing. This constant depends only on $\dim F$ and the estimate includes rank-deficient states, every positive blocklength, and exponentially small smoothing parameters; there is no spectrum-dependent threshold.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 31, Unnumbered Appendix B.3 result: dimension-uniform independent-copy estimate (6.15)

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

/-- Dimension-uniform independent-copy estimate (6.15), PDF pp.31,45.
Every positive blocklength and every 0<v<1, including rank-deficient states. -/
theorem uniformIndependentCopyEntropy [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (n : ℕ) (hn : 1 ≤ n) (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    smoothConditionalMaxEntropy (groupedPower rho n) v ≤
      (n : ℝ) * conditionalEntropy rho + entropyDimensionConstant (Fintype.card A) *
        Real.sqrt ((n : ℝ) * Real.logb 2 (2 / v ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
