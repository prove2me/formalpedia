-- Prove2me | Theorems.Thm_UnderstandingML_uc_implies_agnostic_pac
-- name    : UnderstandingML.uc_implies_agnostic_pac
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:30:10.748801+00:00
-- url     : https://prove2.me/theorems/2950bf16-27de-4e59-85a7-0ea7797f0095
-- title:
--   Corollary 4.4: uniform convergence with m^UC_H implies agnostic PAC learnability by ERM with m_H(ε, δ) ≤ m^UC_H(ε/2, δ)
-- statement:
--   **Corollary 4.4.** If a class $H$ has the uniform convergence property with a function $m^{UC}_H$ then the class is agnostically PAC learnable with the sample complexity $m_H(\epsilon, \delta) \le m^{UC}_H(\epsilon/2, \delta)$. Furthermore, in that case, the $ERM_H$ paradigm is a successful agnostic PAC learner for $H$.
--
--   Formally: if $H$ has the uniform convergence property with $m^{UC}_H$, then every ERM learner for $H$ satisfies the agnostic PAC guarantee (Definition 3.4) with the sample-complexity function $(\epsilon, \delta) \mapsto m^{UC}_H(\epsilon/2, \delta)$, and $H$ is agnostic PAC learnable provided an ERM learner exists.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §4.1 p. 55, Corollary 4.4 (from Lemma 4.2 and Definition 4.3)

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Corollary 4.4** (p. 55). If a class `H` has the uniform convergence property with a function
`m^{UC}_H`, then the class is agnostically PAC learnable with the sample complexity
`m_H(ε, δ) ≤ m^{UC}_H(ε/2, δ)`; furthermore, in that case the `ERM_H` paradigm is a successful
agnostic PAC learner for `H`: every ERM learner satisfies the agnostic PAC guarantee with the
function `(ε, δ) ↦ m^{UC}_H(ε/2, δ)`, and `H` is agnostic PAC learnable as soon as an ERM learner
exists. -/
theorem uc_implies_agnostic_pac {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (mUC : ℝ → ℝ → ℕ)
    (hUC : HasUniformConvergenceWith loss H mUC) :
    (∀ A : Learner Z Hyp, IsERMLearner loss H A →
      IsAgnosticPACWith loss H A (fun ε δ ↦ mUC (ε / 2) δ)) ∧
    ((∃ A : Learner Z Hyp, IsERMLearner loss H A) → AgnosticPACLearnable loss H) := by sorry

end UnderstandingML
