-- Prove2me | Theorems.Thm_UnderstandingML_srm_nonuniform_rate
-- name    : UnderstandingML.srm_nonuniform_rate
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:48:22.099994+00:00
-- url     : https://prove2.me/theorems/425fd626-7337-4492-be03-be1fc540fbd9
-- title:
--   Theorem 7.5: with w(n) = 6/(n²π²) the SRM rule learns H = ⋃ₙ Hₙ nonuniformly with rate m^NUL(ε, δ, h) ≤ m^UC_{H_{n(h)}}(ε/2, 6δ/(πn(h))²)
-- statement:
--   **Theorem 7.5.** Let $H$ be a hypothesis class such that $H = \bigcup_{n \in \mathbb{N}} H_n$, where each $H_n$ has the uniform convergence property with sample complexity $m^{UC}_{H_n}$. Let $w : \mathbb{N} \to [0,1]$ be such that $w(n) = \frac{6}{n^2\pi^2}$. Then $H$ is nonuniformly learnable using the SRM rule with rate
--   $$m^{NUL}_H(\epsilon, \delta, h) \le m^{UC}_{H_{n(h)}}\Big(\epsilon/2, \frac{6\delta}{(\pi n(h))^2}\Big).$$
--
--   Formally: for the family of learners $A_\delta$ implementing the SRM rule with confidence $\delta$ (outputs in $H$, an SRM hypothesis whenever some hypothesis is admissible), with $H_0 = \emptyset$ (the book's indices start at $1$), `IsNonuniformFamilyWith` holds with that rate.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.2 pp. 87-88, Theorem 7.5 with its proof

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 7.5** (p. 87). Let `H = ⋃ₙ Hₙ`, where each `Hₙ` has the uniform convergence
property with sample complexity `m^{UC}_{Hₙ}`, and let `w(n) = 6/(n²π²)`. Then `H` is
nonuniformly learnable using the SRM rule with rate
`m^{NUL}_H(ε, δ, h) ≤ m^{UC}_{H_{n(h)}}(ε/2, 6δ/(π n(h))²)`. Stated for the family of learners
`A δ` implementing the SRM rule with confidence `δ` (outputs in `H`, an SRM hypothesis
whenever one is admissible); the book's indices `n ∈ {1, 2, …}` are the case `H₀ = ∅`. -/
theorem srm_nonuniform_rate {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (Hn : ℕ → Set Hyp) (h0 : Hn 0 = ∅) (mUC : ℕ → ℝ → ℝ → ℕ)
    (hUC : ∀ n, HasUniformConvergenceWith loss (Hn n) (mUC n)) (A : ℝ → Learner Z Hyp)
    (hA : IsSRMFamily loss Hn mUC srmWeight A) :
    IsNonuniformFamilyWith loss (⋃ n, Hn n) A fun ε δ h ↦
      mUC (firstIndex Hn h) (ε / 2) (6 * δ / (Real.pi * firstIndex Hn h) ^ 2) := by sorry

end UnderstandingML
