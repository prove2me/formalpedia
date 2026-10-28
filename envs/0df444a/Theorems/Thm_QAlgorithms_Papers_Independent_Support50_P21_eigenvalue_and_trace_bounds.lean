-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_eigenvalue_and_trace_bounds
-- name    : QAlgorithms.Papers.Independent.Support50.P21.eigenvalue_and_trace_bounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:47:21.931626+00:00
-- url     : https://prove2.me/theorems/9bd17733-7395-41d1-9493-dd116f5b7140
-- title:
--   Lemma 12
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho,\sigma$ be density operators with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Let $\mu_{\min}(\sigma)$ denote the smallest strictly positive eigenvalue. Then
--
--   $$D_{\min}(\rho\Vert\sigma)\le D_{\max}(\rho\Vert\sigma)\le-\log_2\mu_{\min}(\sigma),$$
--   $$D_{\min}(\rho\Vert\sigma)\le-\log_2\!\left(1-\tfrac12\lVert\rho-\sigma\rVert_1\right).$$
--
--   The support hypothesis and normalization keep these logarithms finite. These are both bounds in Lemma 12.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 5, Lemma 12

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

/-- Lemma 12, PDF pp.5–6, (31)–(32): minimum STRICTLY positive eigenvalue,
plus the full-trace-norm bound with exactly the factor 1/2. -/
theorem eigenvalue_and_trace_bounds (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded rho sigma) :
    dMin rho sigma ≤ maxRelative rho sigma ∧
    maxRelative rho sigma ≤ -elog (minPositiveEigenvalue sigma) ∧
    dMin rho sigma ≤ -elog (1 - traceNorm (rho - sigma) / 2) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
