-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_sibson_decomposition_and_minimum
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.sibson_decomposition_and_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:50:08.402095+00:00
-- url     : https://prove2.me/theorems/7faff316-38f1-4538-bde8-6c39ef9970c6
-- title:
--   Unnumbered: decomposition and fixed-law minimum (34)–(36)
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Fix $\alpha>1$ and put $\omega_\alpha(p)=(\sum_xp(x)W_x^\alpha)^{1/\alpha}$, $\sigma_p=\omega_\alpha(p)/\operatorname{Tr}\omega_\alpha(p)$, and $z_\alpha(p)=\frac\alpha{\alpha-1}\log_2\operatorname{Tr}\omega_\alpha(p)$. The trace is positive and $\sigma_p$ is a density operator. For every density $\sigma$,
--
--   $$S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)=z_\alpha(p)+S_\alpha(\sigma_p\|\sigma).$$
--
--   Consequently $\chi_\alpha(p)=z_\alpha(p)$, the minimum is attained at $\sigma_p$, and $\sup_p z_\alpha(p)=\chi^*_{\alpha,1}(W)$. These identities connect the trace formula used in the success bound to the type-1 capacity.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 8, Unnumbered: decomposition and fixed-law minimum (34)–(36)

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

/-- Decomposition and fixed-law minimization (34)–(36), PDF p.8.
The normalized root is constructed from the law, not supplied as an unrelated state. -/
theorem sibson_decomposition_and_minimum {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x))
    (a : ℝ) (ha : 1 < a) :
    (∀ p : FinitelySupportedInputLaw X, 0 < (sibsonRoot a W p).trace.re ∧
      IsDensityMatrix (sibsonCentre a W p) ∧
      (∀ sigma : {A : Operator I // IsDensityMatrix A}, lawObjective a W p sigma.1 =
        sibsonInformation a W p + petzRelativeBits a (sibsonCentre a W p) sigma.1) ∧
      petzLawInformationBits a W p = sibsonInformation a W p ∧
      lawObjective a W p (sibsonCentre a W p) = petzLawInformationBits a W p) ∧
    (⨆ p : FinitelySupportedInputLaw X, sibsonInformation a W p) = capacityOne a W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
