-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_extremeEnhancementIncreasing
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.extremeEnhancementIncreasing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:30:43.916015+00:00
-- url     : https://prove2.me/theorems/0546b9d2-159e-48c7-bbea-2e54aa991c7f
-- title:
--   Strictly increasing extreme-noise capacity enhancement
-- statement:
--   For each integer $d\ge2$, let $\Phi_d$ be the depolarizing channel with parameter $d^2/(d^2-1)$ and define $R_d=C_{\rm ea}(\Phi_d)/C^{(1)}(\Phi_d)$ using the actual capacities. Their exact expressions are the preceding extreme-noise formulas, and $C^{(1)}(\Phi_d)>0$. Then
--
--   $$2\le d<e\ \Longrightarrow\ R_d<R_e,\qquad |R_2-5.0798|<0.00005.$$
--
--   The printed decimal is represented as a four-decimal approximation. This records strict monotonic enhancement; the distinct ambiguous claim about a linear asymptote is explicitly deferred.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 8, §III, unnumbered monotonic enhancement at the extreme parameter

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.8: strict increase of the exact capacity ratio for d>=2.
The printed 5.0798 is a four-decimal approximation; the claimed asymptote is deferred. -/
theorem extremeEnhancementIncreasing :
    StrictMono extremeEnhancement ∧ |extremeEnhancement 0 - 5.0798| < 0.00005 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
