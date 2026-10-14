-- Prove2me | Theorems.Thm_SoftRobust_Duality_scaling_identity
-- name    : SoftRobust.Duality.scaling_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:49:15.548551+00:00
-- url     : https://prove2.me/theorems/ef173a41-017e-4247-96d4-63e6ebcd4959
-- title:
--   Proof of Theorem 2.1, third to fifth equalities: $\inf_{\mathbb Q}\{\mathbb E_{\mathbb Q}[Y]+(\lambda+1)\alpha^Q(\mathbb Q)\} = -(\lambda+1)\rho^Q(Y/(\lambda+1))$
-- statement:
--   Let $\mathbf Q$ be an admissible family of probability measures on $(\Omega,\mathcal F)$ (nondecreasing, convex, $\mathcal Q(0)\ne\emptyset$), with penalty $\alpha^Q$ and generated risk measure $\rho^Q(Y) = \sup_{\mathbb Q}\{-\mathbb E_{\mathbb Q}[Y]-\alpha^Q(\mathbb Q)\}$. For every bounded measurable $Y:\Omega\to\mathbb R$ and every $\lambda \ge 0$,
--
--   $$
--   \inf_{\mathbb Q\in\mathcal P}\big\{\mathbb E_{\mathbb Q}[Y] + (\lambda+1)\,\alpha^Q(\mathbb Q)\big\} = -(\lambda+1)\sup_{\mathbb Q\in\mathcal P}\Big\{-\mathbb E_{\mathbb Q}\Big[\frac{Y}{\lambda+1}\Big] - \alpha^Q(\mathbb Q)\Big\} = -(\lambda+1)\,\rho^Q\Big(\frac{Y}{\lambda+1}\Big).
--   $$
--
--   Applied to $Y = f(x)$, it rewrites the dual function of the previous step through $\rho^Q$, so that the maximum over $\lambda$ becomes $-\min_{\lambda\ge0}\{\lambda\delta + (\lambda+1)\rho^Q(f(x)/(\lambda+1))\}$, the left side of (6).
--
--   **Formalization Note** The infimum on the left is taken in `EReal` (measures with $\alpha^Q = \infty$ contribute $+\infty$); the statement asserts that it equals the real number on the right, so in particular it is finite.
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1224, §2.3, proof of Theorem 2.1, third to fifth equalities ("simple algebra and the definition of ρ^Q")

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- §2.3, proof of Theorem 2.1, p. 1224, third to fifth equalities ("simple algebra and the
definition of ρ^Q"): for every bounded measurable `Y` and `λ ≥ 0`,
`inf_{ℚ ∈ 𝒫} {E_ℚ[Y] + (λ + 1) α^Q(ℚ)} = −(λ + 1) ρ^Q(Y / (λ + 1))`, the infimum taken in `EReal`. -/
theorem scaling_identity {Ω : Type*} [MeasurableSpace Ω]
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (Y : Ω → ℝ) (hY : IsBddPayoff Y) (l : ℝ) (hl : 0 ≤ l) :
    (⨅ Q : ProbabilityMeasure Ω,
        ((∫ ω, Y ω ∂(Q : Measure Ω) : ℝ) : EReal) +
          ((l + 1 : ℝ) : EReal) * (penaltyOfFamily 𝒬 Q : EReal)) =
      ((-((l + 1) * rhoQ 𝒬 (fun ω => Y ω / (l + 1))) : ℝ) : EReal) := by sorry

end SoftRobust.Duality
