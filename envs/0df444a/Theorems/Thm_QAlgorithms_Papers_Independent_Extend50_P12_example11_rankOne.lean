-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_example11_rankOne
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.example11_rankOne
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:52:13.024975+00:00
-- url     : https://prove2.me/theorems/51714e5c-60e5-4ad1-b84d-ea1576306843
-- title:
--   Example 11: rank-one one-to-three evaluation, Eq.(45)
-- statement:
--   Let $d\ge1$, let $\alpha,\beta\in\{1,\ldots,d\}$ be product-basis labels, and let $A=|\alpha\rangle\langle\beta|$. Under Eq. (2)'s permutation convention,
--   $$
--   \begin{aligned}
--   \operatorname{tr}_1\!\left[V(1234)^{T_4}(A\otimes I\otimes I\otimes I)\right]
--   &=\sum_{k,l=1}^d|\alpha\rangle\langle k|\otimes|k\rangle\langle l|\otimes|\beta\rangle\langle l|\\
--   &=\left[(A\otimes I\otimes I)^{R_{3,2}}\right]^{R_{3,1}}.
--   \end{aligned}
--   $$
--   Here $T_4$ is ordinary partial transpose, the partial trace is unnormalized, and $R_{s,t}$ exchanges ket site $s$ with bra site $t$. The first reshuffling is $R_{3,2}$ and the second is $R_{3,1}$.
--
--   This gives both the explicit rank-one output and its ordered-reshuffling form. Direct index substitution confirms that the printed forward-cycle kernel agrees with Eq. (2), contrary to the plan's orientation objection.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 7, Example 11, Eq.(45)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Example 11, PDF pp.7-8, Eq.(45). Both the explicit summed matrix-unit kernel
and the two ordered reshufflings are retained. Under Eq.(2), the named forward
four-cycle expands exactly as its printed kernel; no cycle correction is made. -/
theorem example11_rankOne (d : ℕ) (hd : 0 < d) (alpha beta : Fin d) :
    let L := productInputContraction (r := 1) (m := 3)
      (transposeRegisterSet {3} (permutation d 4 (finRotate 4))) ![Matrix.single alpha beta (1 : ℂ)]
    L = rankOneThreeOutput alpha beta ∧
      L = reshuffleSites 2 0 (reshuffleSites 2 1
        (leadingInput 3 (by omega) (Matrix.single alpha beta (1 : ℂ)))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
