-- Prove2me | Theorems.Thm_UnderstandingML_finite_class_uniform_convergence
-- name    : UnderstandingML.finite_class_uniform_convergence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:31:06.59843+00:00
-- url     : https://prove2.me/theorems/b7e2877e-0478-49b6-a163-0ea4b515d8d4
-- title:
--   Corollary 4.6: a finite class with a [0,1]-valued loss has uniform convergence with m^UC ≤ ⌈log(2|H|/δ)/(2ε²)⌉ and is agnostic PAC learnable by ERM
-- statement:
--   **Corollary 4.6.** Let $H$ be a finite hypothesis class, let $Z$ be a domain, and let $\ell : H \times Z \to [0,1]$ be a loss function. Then $H$ enjoys the uniform convergence property with sample complexity $m^{UC}_H(\epsilon, \delta) \le \lceil \log(2|H|/\delta)/(2\epsilon^2) \rceil$. Furthermore, the class is agnostically PAC learnable using the ERM algorithm with sample complexity $m_H(\epsilon, \delta) \le m^{UC}_H(\epsilon/2, \delta) \le \lceil 2\log(2|H|/\delta)/\epsilon^2 \rceil$.
--
--   Formally: for a finite class $H$ whose losses $\ell(h, \cdot)$ are measurable with values in $[0, 1]$: $H$ has the uniform convergence property with the function $(\epsilon, \delta) \mapsto \lceil \log(2|H|/\delta)/(2\epsilon^2) \rceil$; every ERM learner satisfies the agnostic PAC guarantee with $(\epsilon, \delta) \mapsto \lceil 2\log(2|H|/\delta)/\epsilon^2 \rceil$; and if $H$ is nonempty it is agnostic PAC learnable.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §4.2 pp. 55-57, Corollary 4.6 with its proof (the union bound (4.1) and Hoeffding (4.2))

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Corollary 4.6** (p. 57). Let `H` be a finite hypothesis class, `Z` a domain, and
`ℓ : H × Z → [0, 1]` a loss function. Then `H` enjoys the uniform convergence property with sample
complexity `m^{UC}_H(ε, δ) ≤ ⌈log(2|H|/δ)/(2ε²)⌉`; furthermore, the class is agnostically PAC
learnable using the ERM algorithm with sample complexity
`m_H(ε, δ) ≤ m^{UC}_H(ε/2, δ) ≤ ⌈2 log(2|H|/δ)/ε²⌉`. Stated for a finite class whose losses
`ℓ(h, ·)` are measurable with values in `[0, 1]`; the last clause needs `H` nonempty for an ERM
learner to exist. -/
theorem finite_class_uniform_convergence {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Finset Hyp) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hrange : ∀ h ∈ H, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) :
    HasUniformConvergenceWith loss (↑H) (fun ε δ ↦ ⌈Real.log (2 * H.card / δ) / (2 * ε ^ 2)⌉₊) ∧
    (∀ A : Learner Z Hyp, IsERMLearner loss (↑H) A →
      IsAgnosticPACWith loss (↑H) A (fun ε δ ↦ ⌈2 * Real.log (2 * H.card / δ) / ε ^ 2⌉₊)) ∧
    (H.Nonempty → AgnosticPACLearnable loss (↑H : Set Hyp)) := by sorry

end UnderstandingML
