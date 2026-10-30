-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_hoeffding_duality_and_endpoints
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.hoeffding_duality_and_endpoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:37:35.057722+00:00
-- url     : https://prove2.me/theorems/52b4efa3-c89f-477e-92ca-25595842bff1
-- title:
--   Unnumbered: Hoeffding duality and endpoint limits
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. For density operators $\rho,\sigma$, put $H_r(\rho\|\sigma)=\sup_{0\le a<1}\{-ar/(1-a)+S_a(\rho\|\sigma)\}$ for $r\ge0$. For $0\le\alpha<1$,
--
--   $$S_\alpha(\rho\|\sigma)=-\sup_{r\ge0}\left\{-\frac{r\alpha}{1-\alpha}-H_r(\rho\|\sigma)\right\}.$$
--
--   Furthermore, $\lim_{r\to\infty}H_r=S_0(\rho\|\sigma)\le H_0(\rho\|\sigma)=S_1(\rho\|\sigma)$. Limits and extrema are extended-real ones. Thus these Rényi divergences and Hoeffding distances mutually determine one another, including orthogonal supports.
--
--   The map $r\mapsto H_r(\rho\|\sigma)$ is convex and nonincreasing on $[0,\infty)$.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 4, Unnumbered: Hoeffding duality and endpoint limits

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

/-- Hoeffding duality and both endpoint limits, PDF p.4, following (20).
The convexity and monotonicity on nonnegative rates are included with both endpoint limits. -/
theorem hoeffding_duality_and_endpoints {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : {A : Operator I // IsDensityMatrix A}) :
    (∀ a : ℝ, 0 ≤ a → a < 1 → petzRelativeBits a rho.1 sigma.1 =
      -(⨆ r : {r : ℝ // 0 ≤ r},
        ((-r.1 * a / (1 - a) : ℝ) : EReal) - petzHoeffdingBits r.1 rho.1 sigma.1)) ∧
    Tendsto (fun r : ℝ => petzHoeffdingBits r rho.1 sigma.1) atTop (𝓝 (petzRelativeBits 0 rho.1 sigma.1)) ∧
    petzRelativeBits 0 rho.1 sigma.1 ≤ petzHoeffdingBits 0 rho.1 sigma.1 ∧
    petzHoeffdingBits 0 rho.1 sigma.1 = petzRelativeBits 1 rho.1 sigma.1 ∧
    AntitoneOn (fun r => petzHoeffdingBits r rho.1 sigma.1) (Ici 0) ∧
    (∀ r s t : ℝ, 0 ≤ r → 0 ≤ s → 0 < t → t < 1 →
      petzHoeffdingBits ((1 - t) * r + t * s) rho.1 sigma.1 ≤
        ((1 - t : ℝ) : EReal) * petzHoeffdingBits r rho.1 sigma.1 +
        (t : EReal) * petzHoeffdingBits s rho.1 sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
