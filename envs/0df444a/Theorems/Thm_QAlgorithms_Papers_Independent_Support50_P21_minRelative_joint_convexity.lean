-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_minRelative_joint_convexity
-- name    : QAlgorithms.Papers.Independent.Support50.P21.minRelative_joint_convexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:44:29.351323+00:00
-- url     : https://prove2.me/theorems/9e23d18c-72ff-4041-aca3-27df2e25a470
-- title:
--   Lemma 8
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $K$ be a finite nonempty index set, let $p_i\ge0$ with $\sum_i p_i=1$, and let $\rho_i$ be states and $\sigma_i\ge0$ with $\operatorname{supp}\rho_i\subseteq\operatorname{supp}\sigma_i$. Then
--
--   $$D_{\min}\!\left(\sum_i p_i\rho_i\middle\Vert\sum_i p_i\sigma_i\right)\le\sum_i p_iD_{\min}(\rho_i\Vert\sigma_i).$$
--
--   Zero weights are allowed; the support conditions make every summand finite. This is joint convexity on the proof's stated domain.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 4, Lemma 8

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

/-- Lemma 8, PDF pp.4–5, (24): joint convexity on the precise proof domain.
Zero weights are allowed; support inclusion makes each summand finite. -/
theorem minRelative_joint_convexity {K : Type} [Fintype K] [Nonempty K]
    (p : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (rho sigma : K → Mat I) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hsigma : ∀ i, (sigma i).PosSemidef) (hsupp : ∀ i, SupportIncluded (rho i) (sigma i)) :
    dMin (∑ i, (p i : ℂ) • rho i) (∑ i, (p i : ℂ) • sigma i) ≤
      ∑ i, (p i : EReal) * dMin (rho i) (sigma i) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
