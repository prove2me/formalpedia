-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_maxRelative_equivalent_forms
-- name    : QAlgorithms.Papers.Independent.Support50.P21.maxRelative_equivalent_forms
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:39:47.963556+00:00
-- url     : https://prove2.me/theorems/e75c07f0-39be-4eaa-b0aa-1c92e3b05b39
-- title:
--   §III, equations (7)–(8): equivalent max-relative entropy formulas
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho\ge0$ satisfy $0<\operatorname{Tr}\rho\le1$, and let $\sigma\ge0$ with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. With the inverse square root set to zero on the kernel,
--
--   $$D_{\max}(\rho\Vert\sigma)=\log_2\lambda_{\max}(\sigma^{-1/2}\rho\sigma^{-1/2}).$$
--
--   There is also a least positive $t$ for which
--
--   $$\operatorname{Tr}[\{\rho\ge t\sigma\}(\rho-t\sigma)]=0,$$
--
--   and $D_{\max}(\rho\Vert\sigma)=\log_2t$. The projector includes the zero eigenspace. These are the two equivalent finite formulas for the same divergence.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 3, §III, equations (7)–(8): equivalent max-relative entropy formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- PDF p.3, (7)–(8): nonzero finite domain, generalized inverse square roots,
and an attained LEAST positive threshold for the weak projector. -/
theorem maxRelative_equivalent_forms (rho sigma : Mat I)
    (hrho : IsSubnormalized rho) (hne : 0 < tr rho) (hsigma : sigma.PosSemidef)
    (hsupp : SupportIncluded rho sigma) :
    maxRelative rho sigma = elog (largestEigenvalue
      (supportPower sigma (-(1/2 : ℝ)) * rho * supportPower sigma (-(1/2 : ℝ)))) ∧
    ∃ t : ℝ, IsLeast (thresholdSet rho sigma) t ∧ maxRelative rho sigma = elog t := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
