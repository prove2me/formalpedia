-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_fixed_law_order_monotonicity_and_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.fixed_law_order_monotonicity_and_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:59:27.200607+00:00
-- url     : https://prove2.me/theorems/ad8cde9b-3689-4ecc-bd1d-502f7ffd47e5
-- title:
--   Lemma B.3: monotonicity and order-one limit of fixed-law information
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. For every finite law $p$ on $X$ the map $\alpha\mapsto\chi_\alpha(p)$ is nondecreasing on $[0,\infty)$ and
--
--   $$\lim_{\alpha\to1}\chi_\alpha(p)=\chi_1(p).$$
--
--   For every finite law on $\operatorname{ran}W$, both the same monotonicity and the two-sided limit hold for $\widetilde\chi_\alpha$, defined using the inclusion channel. Compactness of the image is unnecessary. These are the fixed-law continuity facts used before optimization.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 12, Lemma B.3: monotonicity and order-one limit of fixed-law information

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

/-- Lemma B.3, PDF p.12: monotonicity and two-sided order-one convergence for
both finite-law information families, with no compact-image premise. -/
theorem fixed_law_order_monotonicity_and_limit {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) :
    (∀ p : FinitelySupportedInputLaw X,
      MonotoneOn (fun a => petzLawInformationBits a W p) (Ici 0) ∧
      Tendsto (fun a => petzLawInformationBits a W p) (𝓝[≠] 1) (𝓝 (petzLawInformationBits 1 W p))) ∧
    (∀ p : FinitelySupportedInputLaw (Set.range W),
      MonotoneOn (fun a => petzLawInformationBits a (fun rho : Set.range W => rho.1) p) (Ici 0) ∧
      Tendsto (fun a => petzLawInformationBits a (fun rho : Set.range W => rho.1) p) (𝓝[≠] 1)
        (𝓝 (petzLawInformationBits 1 (fun rho : Set.range W => rho.1) p))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
