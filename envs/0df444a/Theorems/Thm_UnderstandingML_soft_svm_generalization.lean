-- Prove2me | Theorems.Thm_UnderstandingML_soft_svm_generalization
-- name    : UnderstandingML.soft_svm_generalization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:39:50.727488+00:00
-- url     : https://prove2.me/theorems/b6e46dc1-5c76-465d-942f-5026921c74a6
-- title:
--   Corollary 15.7 (first parts): for D on the ρ-ball × {±1}, Soft-SVM (15.6) with parameter λ has E_S[L^hinge_D(A(S))], E_S[L^{0−1}_D(A(S))] ≤ L^hinge_D(u) + λ‖u‖² + 2ρ²/(λm) for every u
-- statement:
--   **Corollary 15.7** (first two parts). Let $D$ be a distribution over $X \times \{\pm 1\}$, where $X = \{x : \|x\| \le \rho\}$. Consider running Soft-SVM (Equation (15.6)) on a training set $S \sim D^m$ and let $A(S)$ be the solution of Soft-SVM. Then, for every $u$,
--   $$\mathbb{E}_{S \sim D^m}[L^{hinge}_D(A(S))] \le L^{hinge}_D(u) + \lambda\|u\|^2 + \frac{2\rho^2}{\lambda m}.$$
--   Furthermore, since the hinge loss upper bounds the 0–1 loss we also have $\mathbb{E}_{S \sim D^m}[L^{0-1}_D(A(S))] \le L^{hinge}_D(u) + \lambda\|u\|^2 + \frac{2\rho^2}{\lambda m}$.
--
--   Formally: the support condition holds almost surely, $\lambda > 0$, $m \ge 1$, and the learner is measurable (automatic for the unique minimizer).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.2.1 p. 208, Corollary 15.7 (from Corollary 13.8 and Claim 15.6)

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 15.7** (p. 208), first two parts. Let `D` be a distribution over `X × {±1}` where
`X = {x : ‖x‖ ≤ ρ}`. Consider running Soft-SVM (Equation (15.6)) with parameter `λ` on a
training set `S ∼ D^m` and let `A(S)` be its solution. Then for every `u`,
`E_S[L^hinge_D(A(S))] ≤ L^hinge_D(u) + λ‖u‖² + 2ρ²/(λm)`; and since the hinge loss upper bounds
the 0–1 loss, also `E_S[L^{0−1}_D(A(S))] ≤ L^hinge_D(u) + λ‖u‖² + 2ρ²/(λm)`. The support
condition is almost sure; `A` is measurable (automatic for the unique minimizer). -/
theorem soft_svm_generalization {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {ρ : ℝ} (hρ : 0 < ρ) (hD : ∀ᵐ z ∂D, ‖z.1‖ ≤ ρ ∧ (z.2 = 1 ∨ z.2 = -1)) {lam : ℝ}
    (hlam : 0 < lam) (A : Learner (Vec d × ℝ) (Vec d)) (hA : IsRLMLearner hingeLoss lam A)
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) (u : Vec d) :
    ∫ S, risk hingeLoss D (A m S) ∂(iidLaw D m) ≤
        risk hingeLoss D u + lam * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) ∧
    ∫ S, risk zeroOneLoss D (A m S) ∂(iidLaw D m) ≤
        risk hingeLoss D u + lam * ‖u‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) := by sorry

end UnderstandingML
