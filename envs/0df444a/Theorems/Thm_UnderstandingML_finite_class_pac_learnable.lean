-- Prove2me | Theorems.Thm_UnderstandingML_finite_class_pac_learnable
-- name    : UnderstandingML.finite_class_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:28:00.172201+00:00
-- url     : https://prove2.me/theorems/0950d7b2-7177-45b8-870c-ced7185ab432
-- title:
--   Corollary 3.2: every finite hypothesis class is PAC learnable, by ERM, with sample complexity m_H(ε, δ) ≤ ⌈log(|H|/δ)/ε⌉
-- statement:
--   **Corollary 3.2.** Every finite hypothesis class is PAC learnable with sample complexity $m_H(\epsilon, \delta) \le \lceil \log(|H|/\delta)/\epsilon \rceil$.
--
--   Formally: for a nonempty finite class $H$ of measurable hypotheses $X \to \{0,1\}$, there is a learning algorithm implementing the $ERM_H$ rule that PAC learns $H$ (Definition 3.1) with the sample-complexity function $(\epsilon, \delta) \mapsto \lceil \log(|H|/\delta)/\epsilon \rceil$; in particular $H$ is PAC learnable.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §3.1 p. 44, Corollary 3.2 (rephrasing Corollary 2.3 in the PAC model)

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Corollary 3.2** (p. 44). Every finite hypothesis class is PAC learnable with sample complexity
`m_H(ε, δ) ≤ ⌈log(|H|/δ)/ε⌉`, and (Corollary 2.3) the `ERM_H` rule is a successful learner:
for a nonempty finite class of measurable hypotheses there is an ERM learner that PAC learns `H`
with the sample-complexity function `(ε, δ) ↦ ⌈log(|H|/δ)/ε⌉`; in particular `H` is PAC
learnable. -/
theorem finite_class_pac_learnable {X : Type*} [MeasurableSpace X] (H : Finset (X → Bool))
    (hne : H.Nonempty) (hH : ∀ h ∈ H, Measurable h) :
    (∃ A : Learner (X × Bool) (X → Bool), IsERMLearner loss01 (↑H) A ∧
      IsPACWith (↑H) A (fun ε δ ↦ ⌈Real.log (H.card / δ) / ε⌉₊)) ∧
    PACLearnable (↑H : Set (X → Bool)) := by sorry

end UnderstandingML
