-- Prove2me | Theorems.Thm_UnderstandingML_log_loss_risk_decomposition
-- name    : UnderstandingML.log_loss_risk_decomposition
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:32:10.545031+00:00
-- url     : https://prove2.me/theorems/11b5effd-e761-48cf-b5b5-1e290ad69855
-- title:
--   Equation (24.5): under a distribution P on a finite domain, the true log-loss risk of θ is D_RE[P‖P_θ] + H(P)
-- statement:
--   **Equation (24.5).** Assuming that the data is distributed according to a distribution $P$ (not necessarily of the parametric form we employ), the true risk of a parameter $\theta$ becomes
--   $$\mathbb{E}_x[\ell(\theta, x)] = -\sum_x P[x]\log(P_\theta[x]) = \underbrace{\sum_x P[x]\log\frac{P[x]}{P_\theta[x]}}_{D_{RE}[P\|P_\theta]} + \underbrace{\sum_x P[x]\log\frac{1}{P[x]}}_{H(P)}.$$
--
--   Formally: on a finite domain, $P$ a probability mass function and $P_\theta$ positive.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.1.2 p. 345, Equation (24.5)

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Equation (24.5)** (p. 345). For data distributed according to a distribution `P` over a
finite domain, the true risk of the parameter `θ` under the log-loss is
`E_x[ℓ(θ, x)] = −∑ₓ P[x] log(P_θ[x]) = D_RE[P‖P_θ] + H(P)`. `P_θ` is positive. -/
theorem log_loss_risk_decomposition {Θ X : Type*} [Fintype X] (P : X → ℝ) (hP : IsPMF P)
    (Pθ : Θ → X → ℝ) (θ : Θ) (hpos : ∀ x, 0 < Pθ θ x) :
    ∑ x, P x * logLoss Pθ θ x = relEntropy P (Pθ θ) + entropy P := by sorry

end UnderstandingML
