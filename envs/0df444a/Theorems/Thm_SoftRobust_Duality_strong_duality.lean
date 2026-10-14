-- Prove2me | Theorems.Thm_SoftRobust_Duality_strong_duality
-- name    : SoftRobust.Duality.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:49:16.283462+00:00
-- url     : https://prove2.me/theorems/8202729b-efdb-4aec-9d77-01aad99b90ee
-- title:
--   Proof of Theorem 2.1, second equality: strong Lagrange duality with an attained dual optimum ($\delta>0$)
-- statement:
--   Work in the soft robust model with an admissible family $\mathbf Q$ and its penalty $\alpha^Q$. Let $\delta > 0$ and $x \in X$. Then the maximum below is attained, and
--
--   $$
--   \inf\big\{\mathbb E_{\mathbb Q}[f(x)] + \alpha^Q(\mathbb Q) : \mathbb Q \in \mathcal P,\ \alpha^Q(\mathbb Q)\le\delta\big\} = \max_{\lambda\ge0}\Big\{-\lambda\delta + \inf_{\mathbb Q\in\mathcal P}\big\{\mathbb E_{\mathbb Q}[f(x)] + (\lambda+1)\,\alpha^Q(\mathbb Q)\big\}\Big\}.
--   $$
--
--   This is Lagrange duality for the convex program over measures with the one constraint $\alpha^Q(\mathbb Q) \le \delta$: since $\delta > 0$ and $\mathcal Q(0)$ is nonempty, any $\mathbb Q \in \mathcal Q(0)$ is a Slater point, and the primal value is finite because $f(x)$ is bounded. It is the step that turns the soft robust constraint into a constraint with a single scalar multiplier $\lambda$.
--
--   **Formalization Note** The claim is `IsGreatest` of the set of dual values $\{D(\lambda) : \lambda \ge 0\}$ at the primal value, i.e. some $\lambda_0 \ge 0$ has $D(\lambda_0)$ equal to the primal value and $D(\lambda)$ is at most it for every $\lambda \ge 0$. All infima are in `EReal`; a measure with $\alpha^Q(\mathbb Q) = \infty$ contributes $+\infty$ to the inner infimum.
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1224, §2.3, proof of Theorem 2.1, second equality (Slater condition, Luenberger 1969, Ch. 8)

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- §2.3, proof of Theorem 2.1, p. 1224, second equality (δ > 0, Slater): strong Lagrange duality
with attainment of the dual optimum,
`inf{E_ℚ[f(x)] + α^Q(ℚ) : α^Q(ℚ) ≤ δ} = max_{λ ≥ 0} {−λδ + inf_{ℚ ∈ 𝒫} {E_ℚ[f(x)] + (λ + 1) α^Q(ℚ)}}`.
All infima are in `EReal`; a measure with `α^Q(ℚ) = ∞` contributes `+∞`. -/
theorem strong_duality {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (M : Model Ω n m)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M.X) :
    IsGreatest
      ((fun l : ℝ => ((-(l * δ) : ℝ) : EReal) +
          ⨅ Q : ProbabilityMeasure Ω,
            ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) +
              ((l + 1 : ℝ) : EReal) * (penaltyOfFamily 𝒬 Q : EReal)) '' Set.Ici 0)
      (⨅ (Q : ProbabilityMeasure Ω) (_ : penaltyOfFamily 𝒬 Q ≤ ENNReal.ofReal δ),
        ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal)) := by sorry

end SoftRobust.Duality
