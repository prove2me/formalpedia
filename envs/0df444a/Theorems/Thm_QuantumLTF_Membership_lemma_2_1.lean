-- Prove2me | Theorems.Thm_QuantumLTF_Membership_lemma_2_1
-- name    : QuantumLTF.Membership.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:04.707287+00:00
-- url     : https://prove2.me/theorems/3322d7fb-abd8-4575-94d1-2c044a17e1d7
-- title:
--   Lemma 2.1 — Gaussian disagreement of LTFs
-- statement:
--   Let $w_1,w_2\in\mathbb S^{n-1}$ and $\theta_1,\theta_2\in\mathbb R$. Then
--   $$\Pr_{x\sim\gamma_n}[f_{w_1,\theta_1}(x)\ne f_{w_2,\theta_2}(x)]\le\frac12\|w_1-w_2\|+\frac{|\theta_1-\theta_2|}{\sqrt{2\pi}},$$
--   and, in the homogeneous case $\theta_1=\theta_2=0$,
--   $$\Pr_{x\sim\gamma_n}[f_{w_1}(x)\ne f_{w_2}(x)]=\frac1\pi\arccos(\langle w_1,w_2\rangle).$$
--   The first bound turns parameter error into classification error. It is the last step of the learner's analysis.
--
--   Differences from the source: none.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 2.1, Eqs. (14), (15), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree

namespace QuantumLTF.Membership

/-- **Lemma 2.1 (Gaussian disagreement of LTFs).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Lemma 2.1, p. 17 (PDF p. 18), Eqs. (14), (15).
For unit `w₁, w₂` and `θ₁, θ₂`,
`Pr[f_{w₁,θ₁} ≠ f_{w₂,θ₂}] ≤ ‖w₁ − w₂‖ / 2 + |θ₁ − θ₂| / √(2π)`; and for `θ₁ = θ₂ = 0` the disagreement
equals `arccos(⟨w₁, w₂⟩) / π`.

**Formalization Note.** Both clauses are in one statement. The source puts no bound on `n`; the
sphere is empty at `n = 0`. -/
theorem lemma_2_1 {n : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin n)) (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1)
    (θ₁ θ₂ : ℝ) :
    disagree (ltf w₁ θ₁) (ltf w₂ θ₂) ≤ ‖w₁ - w₂‖ / 2 + |θ₁ - θ₂| / Real.sqrt (2 * Real.pi) ∧
      disagree (ltf w₁ 0) (ltf w₂ 0) = Real.arccos (inner ℝ w₁ w₂) / Real.pi := by sorry

end QuantumLTF.Membership
