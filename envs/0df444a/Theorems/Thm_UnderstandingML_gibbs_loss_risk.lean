-- Prove2me | Theorems.Thm_UnderstandingML_gibbs_loss_risk
-- name    : UnderstandingML.gibbs_loss_risk
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:06:42.546561+00:00
-- url     : https://prove2.me/theorems/42428510-3dcc-4af3-83cb-a5996bbef6ab
-- title:
--   §31.1: by linearity of expectation the generalization loss of the randomized rule Q is E_{z∼D}[ℓ(Q,z)] = E_{h∼Q}[L_D(h)] = L_D(Q)
-- statement:
--   **§31.1 (p. 415).** We define the loss of $Q$ on an example $z$ to be $\ell(Q, z) = \mathbb{E}_{h \sim Q}[\ell(h, z)]$. By the linearity of expectation, the generalization loss and training loss of $Q$ can be written as $L_D(Q) = \mathbb{E}_{h \sim Q}[L_D(h)]$ and $L_S(Q) = \mathbb{E}_{h \sim Q}[L_S(h)]$.
--
--   Formally: $\mathbb{E}_{z \sim D}[\ell(Q, z)] = \mathbb{E}_{h \sim Q}[L_D(h)]$ for a jointly measurable $[0,1]$-valued loss (Fubini).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.1 p. 415, the definitions of ℓ(Q, z) and L_D(Q)

import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory

namespace UnderstandingML

/-- **§31.1** (p. 415). By the linearity of expectation, the generalization loss of the
randomized rule `Q` is `E_{z ∼ D}[ℓ(Q, z)] = E_{h ∼ Q}[L_D(h)] = L_D(Q)`. The loss is jointly
measurable and bounded, `D` and `Q` probability measures. -/
theorem gibbs_loss_risk {Z Hyp : Type*} [MeasurableSpace Z] [MeasurableSpace Hyp]
    (loss : Hyp → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (Q : Measure Hyp) [IsProbabilityMeasure Q] :
    ∫ z, gibbsLoss loss Q z ∂D = gibbsRisk loss D Q := by sorry

end UnderstandingML
