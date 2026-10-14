-- Prove2me | Theorems.Thm_SoftRobust_Duality_inf_reparam
-- name    : SoftRobust.Duality.inf_reparam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:49:19.98039+00:00
-- url     : https://prove2.me/theorems/00380182-10b6-41bd-8d64-2aed06fb4fde
-- title:
--   Proof of Theorem 2.1, first equality: the soft robust infimum rewritten through $\alpha^Q$ ($\delta>0$)
-- statement:
--   Work in the soft robust model with an admissible family $\mathbf Q$ (nondecreasing, convex, $\mathcal Q(0)\neq\emptyset$) and its penalty $\alpha^Q(\mathbb Q) = \inf\{\varepsilon\ge0 : \mathbb Q\in\mathcal Q(\varepsilon)\}$. Let $\delta > 0$ and $x \in X$. Then
--
--   $$
--   \inf\big\{\mathbb E_{\mathbb Q}[f(x)] + \varepsilon : \varepsilon \in [0,\delta],\ \mathbb Q \in \mathcal Q(\varepsilon)\big\} = \inf\big\{\mathbb E_{\mathbb Q}[f(x)] + \alpha^Q(\mathbb Q) : \mathbb Q \in \mathcal P,\ \alpha^Q(\mathbb Q) \le \delta\big\}.
--   $$
--
--   The left side is the quantity whose sign decides membership of $x$ in the soft robust set $X^Q(\delta)$; the right side is the primal value of a convex program over measures with the single constraint $\alpha^Q(\mathbb Q)\le\delta$, to which Lagrange duality is applied next.
--
--   **Formalization Note** Both infima are taken in the extended reals `EReal`. A measure with $\alpha^Q(\mathbb Q)=\delta$ need not lie in $\mathcal Q(\delta)$ (the infimum defining $\alpha^Q$ need not be attained), so the statement keeps the admissibility of the family and the boundedness of $f(x)$ that come with the model.
-- source:
--   Ben-Tal, Bertsimas, Brown, A Soft Robust Model for Optimization Under Ambiguity, Oper. Res. 58(4) (2010), p. 1224, §2.3, proof of Theorem 2.1, first equality

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobust.Duality

/-- §2.3, proof of Theorem 2.1, p. 1224, first equality (δ > 0): the soft robust infimum
`inf{E_ℚ[f(x)] + ε : ε ∈ [0, δ], ℚ ∈ 𝒬(ε)}` equals `inf{E_ℚ[f(x)] + α^Q(ℚ) : ℚ ∈ 𝒫, α^Q(ℚ) ≤ δ}`.
Both infima are taken in `EReal` (an empty infimum is `+∞`). -/
theorem inf_reparam {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (M : Model Ω n m)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M.X) :
    (⨅ (ε : ℝ≥0) (_ : (ε : ℝ) ≤ δ) (Q : ProbabilityMeasure Ω) (_ : Q ∈ 𝒬 ε),
        (((∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + (ε : ℝ) : ℝ) : EReal)) =
      ⨅ (Q : ProbabilityMeasure Ω) (_ : penaltyOfFamily 𝒬 Q ≤ ENNReal.ofReal δ),
        ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) + (penaltyOfFamily 𝒬 Q : EReal) := by sorry

end SoftRobust.Duality
