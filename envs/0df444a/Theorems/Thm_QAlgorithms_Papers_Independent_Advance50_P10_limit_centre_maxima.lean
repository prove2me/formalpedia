-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_limit_centre_maxima
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.limit_centre_maxima
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:46:47.758991+00:00
-- url     : https://prove2.me/theorems/3be98b5c-c202-4dc6-b36a-147822ddead3
-- title:
--   Remark IV.6: maxima at the limit centre
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. Let $\sigma_0$ be a limit of regularized minimizing centres along positive perturbations tending to zero. Then
--
--   $$\sup_{p\in\mathcal M(K)}f_{\alpha,0}(p,\sigma_0)=\max_{p\in\mathcal M(K)}f_{\alpha,0}(p,\sigma_0),\qquad\sup_{\rho\in K}S_\alpha(\rho\|\sigma_0)=\max_{\rho\in K}S_\alpha(\rho\|\sigma_0).$$
--
--   These are precisely the first supremum in (28) and the last one in (29). No maximizing law for the separate maximin expression is asserted.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 7, Remark IV.6: maxima at the limit centre

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Remark IV.6, PDF p.7: exactly the two indicated suprema attain maxima
at the limit centre. No general maximizing law for sup_p min_sigma is asserted. -/
theorem limit_centre_maxima {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1)
    (centres : ℝ → {A : Operator I // IsDensityMatrix A}) (hcentres : CentreFamily K false a centres)
    (sigma : {A : Operator I // IsDensityMatrix A}) (hlimit : CentreLimit centres sigma) :
    ReachesMaximum (fun p : ProbabilityMeasure K => measureObjective K false a 0 p sigma) ∧
    ReachesMaximum (pointObjective K false a 0 sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
