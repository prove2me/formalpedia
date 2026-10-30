-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_optimal_helstrom_mixture
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.optimal_helstrom_mixture
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:52:20.19998+00:00
-- url     : https://prove2.me/theorems/6615b3ae-5ece-45d8-83cd-b2dc6f0237af
-- title:
--   Unnumbered: optimal Helstrom mixing parameter and centre
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $r\ge1$ and let $\rho_1,\ldots,\rho_r$ be density operators. Define $S_{\max}(\rho\|\sigma)=\inf\{\log_2\lambda:\lambda>0,\ \rho\le\lambda\sigma\}$ and $R_{\max}=\inf_{\sigma\in\mathcal S(H)}\max_iS_{\max}(\rho_i\|\sigma)$. Then the largest $q\in[0,1]$ for which there exist densities $\tau_i$ and a common density $\sigma$ with $\sigma=q\rho_i+(1-q)\tau_i$ for every $i$ is
--
--   $$q=2^{-R_{\max}}.$$
--
--   Every common mixture at this optimal weight is an $S_{\max}$-centre: $\max_iS_{\max}(\rho_i\|\sigma)=R_{\max}$. Identical families, including a singleton, have $q=1$ and need no division by $1-q$. This gives a geometric characterization of the max-divergence centre.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 9, Unnumbered: optimal Helstrom mixing parameter and centre

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

/-- Optimal Helstrom common-mixture parameter and centre, PDF p.9.
The common mixture is feasible at the computed largest q, even for identical states. -/
theorem optimal_helstrom_mixture {I : Type} [Fintype I] [DecidableEq I]
    (r : ℕ) (hr : 0 < r) (rho : Fin r → Operator I) (hstates : ∀ i, IsDensityMatrix (rho i)) :
    IsGreatest {q : ℝ | CommonMixture rho q} (helstromWeight rho) ∧
    (∀ sigma : {A : Operator I // IsDensityMatrix A}, ∀ tau : Fin r → {A : Operator I // IsDensityMatrix A},
      (∀ i, sigma.1 = (helstromWeight rho : ℂ) • rho i +
        ((1 - helstromWeight rho : ℝ) : ℂ) • (tau i).1) →
      (⨆ i, maxRelative (rho i) sigma.1) = divergenceRadiusBits maxRelative rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
