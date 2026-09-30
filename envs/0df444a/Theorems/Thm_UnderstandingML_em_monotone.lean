-- Prove2me | Theorems.Thm_UnderstandingML_em_monotone
-- name    : UnderstandingML.em_monotone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:31:02.38152+00:00
-- url     : https://prove2.me/theorems/3e2d1818-69c3-4acb-a6ae-3aacb2cf424a
-- title:
--   Theorem 24.3: the EM procedure never decreases the log-likelihood, L(θ⁽ᵗ⁺¹⁾) ≥ L(θ⁽ᵗ⁾)
-- statement:
--   **Theorem 24.3.** The EM procedure never decreases the log-likelihood; namely, for all $t$, $L(\theta^{(t+1)}) \ge L(\theta^{(t)})$.
--
--   Formally: for a positive parametric joint $P_\theta[X = x, Y = y]$ (so every logarithm is genuine), a sample, and any run of EM in which each M-step returns some maximizer of $F(Q^{(t+1)}, \cdot)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.4.1 p. 352, Theorem 24.3 with its proof

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 24.3** (p. 352). The EM procedure never decreases the log-likelihood; namely, for
all `t`, `L(θ⁽ᵗ⁺¹⁾) ≥ L(θ⁽ᵗ⁾)`. The joint `P_θ[X = x, Y = y]` is positive, so that all
logarithms are genuine. -/
theorem em_monotone {Θ X : Type*} {k m : ℕ} (p : Θ → X → Fin k → ℝ)
    (hp : ∀ θ x y, 0 < p θ x y) (x : Fin m → X) (θ : ℕ → Θ) (hθ : IsEMSequence p x θ) (t : ℕ) :
    latentLogLik p x (θ t) ≤ latentLogLik p x (θ (t + 1)) := by sorry

end UnderstandingML
