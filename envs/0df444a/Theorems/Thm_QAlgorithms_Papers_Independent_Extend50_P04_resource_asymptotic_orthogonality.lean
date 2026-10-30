-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_resource_asymptotic_orthogonality
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.resource_asymptotic_orthogonality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:15:03.552471+00:00
-- url     : https://prove2.me/theorems/79ec9ac5-a44c-4c55-bfae-f91b7eb9916d
-- title:
--   Figure 5 / §VI: asymptotic orthogonality of qubit resources
-- statement:
--   For each $N$, let $O_N$ be the optimized qubit resource operation constructed by (84) using the normalized explicit coefficients (87)/(E5), and let $R_{N,2}=|\langle\Phi^+|(O_N\otimes I)|\Phi^+\rangle|$. At fixed local dimension two,
--   $$\lim_{N\to\infty}R_{N,2}=0.$$
--   Thus the two families of full resource states become orthogonal asymptotically. No finite-port orthogonality or all-d rate is asserted.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 18, Figure 5 / §VI: asymptotic orthogonality of qubit resources

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.18, Figure 5 and section VI: asymptotic orthogonality at fixed local dimension two.
This is the source's explicit limit claim, not a finite-N inequality inferred from a graph. -/
theorem resource_asymptotic_orthogonality :
    Filter.Tendsto (fun N => resourceFidelity 2 N (resourceOperation 2 N (qubitCoefficients N)))
      Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
