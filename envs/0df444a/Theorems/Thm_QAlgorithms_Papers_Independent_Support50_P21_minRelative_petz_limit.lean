-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_minRelative_petz_limit
-- name    : QAlgorithms.Papers.Independent.Support50.P21.minRelative_petz_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:40:38.301688+00:00
-- url     : https://prove2.me/theorems/cdd6556b-6eb6-4a76-93bb-1c5b4e34bd88
-- title:
--   §III, equation (10): order-zero Petz limit
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho\ge0$ with $0<\operatorname{Tr}\rho\le1$, and let $\sigma\ge0$. For $0<\alpha<1$ define the unnormalized Petz expression
--
--   $$S_\alpha(\rho\Vert\sigma)=\frac{\log_2\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})}{\alpha-1}.$$
--
--   Then, in the extended real topology,
--
--   $$\lim_{\alpha\downarrow0}S_\alpha(\rho\Vert\sigma)=D_{\min}(\rho\Vert\sigma)=-\log_2\operatorname{Tr}(\pi_\rho\sigma).$$
--
--   The support projector is $\pi_\rho$; zero overlap gives $+\infty$. There is no division by $\operatorname{Tr}\rho$. This identifies the order-zero divergence.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 3, §III, equation (10): order-zero Petz limit

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

/-- PDF p.3, (10)–(11): unnormalized Petz right-hand limit; orthogonal support
has value +infinity. The order is restricted to (0,1). -/
theorem minRelative_petz_limit (rho sigma : Mat I)
    (hrho : IsSubnormalized rho) (hne : 0 < tr rho) (hsigma : sigma.PosSemidef) :
    Tendsto (fun alpha => unnormalizedPetz alpha rho sigma) (nhdsWithin 0 (Set.Ioo 0 1))
      (nhds (dMin rho sigma)) ∧
    (tr (support rho * sigma) = 0 → dMin rho sigma = ⊤) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
