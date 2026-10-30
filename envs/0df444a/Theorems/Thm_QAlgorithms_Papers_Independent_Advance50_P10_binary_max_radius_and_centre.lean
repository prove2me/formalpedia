-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_binary_max_radius_and_centre
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.binary_max_radius_and_centre
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:53:10.356243+00:00
-- url     : https://prove2.me/theorems/ef4c9544-01bf-47f9-80c0-55e9bbbcf561
-- title:
--   Unnumbered: binary max-radius and corrected centre
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $\rho_1,\rho_2$ be densities, set $X=\rho_1-\rho_2$, let $X_+,X_-$ be its positive and negative parts, and put $D=\frac12\|X\|_1$. With $S_{\max}(\rho\|\sigma)=\inf\{\log_2\lambda:\rho\le\lambda\sigma,\lambda>0\}$ and its density-centre radius $R_{\max}$,
--
--   $$R_{\max}(\{\rho_1,\rho_2\})=\log_2(1+D),\qquad\sigma_* =\frac{\rho_1+X_-}{1+D}=\frac{\rho_2+X_+}{1+D}.$$
--
--   The operator $\sigma_*$ is a density and attains the radius. **Source correction:** the printed factors $2$ and the placement of $X_+,X_-$ do not produce a normalized common mixture. The displayed corrected formula is forced by the common-mixture construction; independently audited in moderation round 1.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 9, Unnumbered: binary max-radius and corrected centre

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

/-- Binary max-radius and corrected centre, PDF p.9.
SOURCE CORRECTION: printed (rho1+2 Xplus)/(1+D)=(rho2+2 Xminus)/(1+D)
is changed to (rho1+Xminus)/(1+D)=(rho2+Xplus)/(1+D), where X=rho1-rho2.
The printed expression is not normalized; the corrected numerators agree and have trace 1+D.
The correction requires independent moderation. -/
theorem binary_max_radius_and_centre {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : {A : Operator I // IsDensityMatrix A}) :
    let D := traceNorm (rho.1 - sigma.1) / 2
    let centre := (((1 + D)⁻¹ : ℝ) : ℂ) • (rho.1 + positivePart (sigma.1 - rho.1))
    divergenceRadiusBits maxRelative (pairFamily rho.1 sigma.1) = (Real.logb 2 (1 + D) : EReal) ∧
    centre = (((1 + D)⁻¹ : ℝ) : ℂ) • (sigma.1 + positivePart (rho.1 - sigma.1)) ∧
    IsDensityMatrix centre ∧
    (⨆ i : Fin 2, maxRelative (pairFamily rho.1 sigma.1 i) centre) =
      divergenceRadiusBits maxRelative (pairFamily rho.1 sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
