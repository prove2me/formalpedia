-- Prove2me | Theorems.Thm_UnderstandingML_em_alternate_max
-- name    : UnderstandingML.em_alternate_max
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:31:42.041626+00:00
-- url     : https://prove2.me/theorems/41a8f7ef-db8c-4348-bda5-3b7beb945835
-- title:
--   Lemma 24.2: G(Q, θ) ≤ L(θ) for all Q ∈ 𝒬 with equality at the posterior Q_{i,y} = P_θ[Y = y | X = xᵢ], and the maximizers of G(Q, ·) and F(Q, ·) coincide
-- statement:
--   **Lemma 24.2.** The EM procedure can be rewritten as $Q^{(t+1)} = \operatorname{argmax}_{Q \in \mathcal{Q}} G(Q, \theta^{(t)})$, $\theta^{(t+1)} = \operatorname{argmax}_\theta G(Q^{(t+1)}, \theta)$. Furthermore, $G(Q^{(t+1)}, \theta^{(t)}) = L(\theta^{(t)})$.
--
--   Formally, for a positive joint: (i) $G(Q, \theta) \le L(\theta)$ for every $Q \in \mathcal{Q}$ (Jensen); (ii) the posterior $Q_{i,y} = P_\theta[Y = y \mid X = x_i]$ attains $G(Q, \theta) = L(\theta)$, hence is a maximizer over $\mathcal{Q}$; (iii) for fixed $Q$, $G(Q, \theta) \le G(Q, \theta')$ iff $F(Q, \theta) \le F(Q, \theta')$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.4.1 pp. 351-352, Lemma 24.2 with its proof

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 24.2** (p. 351). The EM procedure can be rewritten as
`Q⁽ᵗ⁺¹⁾ = argmax_{Q ∈ 𝒬} G(Q, θ⁽ᵗ⁾)`, `θ⁽ᵗ⁺¹⁾ = argmax_θ G(Q⁽ᵗ⁺¹⁾, θ)`; furthermore
`G(Q⁽ᵗ⁺¹⁾, θ⁽ᵗ⁾) = L(θ⁽ᵗ⁾)`. Stated as: for every `Q ∈ 𝒬`, `G(Q, θ) ≤ L(θ)`; the posterior
`Q_{i,y} = P_θ[Y = y | X = xᵢ]` attains `G(Q, θ) = L(θ)`; and for fixed `Q` the maximizers of
`G(Q, ·)` and `F(Q, ·)` coincide. The joint is positive. -/
theorem em_alternate_max {Θ X : Type*} {k m : ℕ} (p : Θ → X → Fin k → ℝ)
    (hp : ∀ θ x y, 0 < p θ x y) (x : Fin m → X) :
    (∀ (Q : Fin m → Fin k → ℝ) (θ : Θ), IsRowStochastic Q → emG p x Q θ ≤ latentLogLik p x θ) ∧
    (∀ θ : Θ, emG p x (fun i y ↦ posterior p θ (x i) y) θ = latentLogLik p x θ) ∧
    (∀ (Q : Fin m → Fin k → ℝ) (θ θ' : Θ), emG p x Q θ ≤ emG p x Q θ' ↔ emF p x Q θ ≤ emF p x Q θ') := by sorry

end UnderstandingML
