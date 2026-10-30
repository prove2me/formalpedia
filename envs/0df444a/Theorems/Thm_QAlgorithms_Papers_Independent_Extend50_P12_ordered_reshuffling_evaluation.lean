-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_ordered_reshuffling_evaluation
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.ordered_reshuffling_evaluation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:52:43.456751+00:00
-- url     : https://prove2.me/theorems/df037603-03b4-4f7d-bbb4-d14028e4c0c1
-- title:
--   Proposition 12: ordered sequence of reshufflings, Eq.(46)
-- statement:
--   Let $d\ge1$, let $n\ge2$ be the number of output registers, and put $k=n+1\ge3$. For arbitrary $A\in M_d(\mathbb C)$, with the fixed product-basis permutation action and ordinary partial transpose,
--   $$
--   \operatorname{tr}_1\!\left[V(1\cdots k)^{T_k}(A\otimes I^{\otimes n})\right]
--   =\left[\cdots\left[(A\otimes I^{\otimes(n-1)})^{R_{n,n-1}}\right]^{R_{n,n-2}}\cdots\right]^{R_{n,1}}.
--   $$
--   Each $R_{s,t}$ exchanges ket site $s$ with bra site $t$. The displayed order is applied from $R_{n,n-1}$ down to $R_{n,1}$, and the trace is unnormalized. This is the domain where the printed sequence has no site-zero endpoint.
--
--   The identity replaces the given contraction by a specified sequence of reshufflings. Appendix C's matrix-unit expansion agrees with Eq. (2); its orientation is unchanged.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 7, Proposition 12, Eq.(46); Appendix C, Eq.(C5)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Proposition 12, PDF p.7, Eq.(46), and p.14, Eq.(C5). There are n=k-1>=2
outputs, the domain where the printed ordered reshuffling sequence is defined.
The partial transpose on the last input/output-kernel site is retained.
Appendix C's cycle expansion agrees with Eq.(2), contrary to the plan's audit. -/
theorem ordered_reshuffling_evaluation (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (A : LocalMatrix d) :
    productInputContraction (r := 1) (m := n)
      (transposeRegisterSet {⟨n, by omega⟩} (permutation d (1 + n) (finRotate (1 + n))))
      ![A] =
    orderedReshuffles n hn (leadingInput n (by omega) A) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
