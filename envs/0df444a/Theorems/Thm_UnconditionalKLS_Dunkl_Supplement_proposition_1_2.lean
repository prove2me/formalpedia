-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_Supplement_proposition_1_2
-- name    : UnconditionalKLS.Dunkl.Supplement.proposition_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:16:16.723481+00:00
-- url     : https://prove2.me/theorems/722d6004-ea83-43ae-9e35-fb68ea970b95
-- title:
--   Proposition 1.2 — improved Brascamp–Lieb inequality $C_P(\nu)\le\|\mathbb E_\nu[(\nabla^2W)^{-1}]\|_{op}$
-- statement:
--   Let $\Omega\subset\mathbb R^n$ be an open convex set and let $W:\Omega\to\mathbb R$ be twice continuously differentiable, with $\int_\Omega e^{-W}\,dx = 1$, so that $\nu = \mathbf 1_\Omega e^{-W}\,dx$ is a probability measure. Assume the Hessian $\nabla^2W(x)$ is positive definite at every $x\in\Omega$. Then the Poincaré constant of $\nu$ is bounded by the operator norm of the averaged inverse Hessian:
--
--   $$C_P(\nu)\le\big\|\mathbb E_\nu\big[(\nabla^2W)^{-1}\big]\big\|_{op}.$$
--
--   Here $\|\cdot\|_{op}$ is the $\ell^2\to\ell^2$ operator norm, and the right side is $+\infty$ when the inverse Hessian is not $\nu$-integrable. The classical Brascamp–Lieb inequality gives the weaker bound $\sup_x\|(\nabla^2W(x))^{-1}\|_{op}$; averaging is what lets the second proof of the main theorem use measures with flat potentials after a change of variables (Proposition 4.2).
--
--   **Formalization Note** $W$ is a function on all of $\mathbb R^n$ whose values off $\Omega$ are irrelevant; $C^2$ is `ContDiffOn ℝ 2 W Ω`. The expectation is entrywise, and $C_P$ is the base optimal Poincaré constant with ambient locally Lipschitz tests, as in (1.1).
--
--   Differences from the source:
--   - reading: (∇²W)^{-1} with no stated sign condition on ∇²W → ∇²W(x) positive definite at every x ∈ Ω; reason: the printed inverse needs invertibility and the proof (p. 28) uses "Since H is positive definite"; invertibility alone is false: W(x,y) = (x² − y²)/2 + c on a large square (−L, L)² has ‖𝔼[H^{-1}]‖_op = 1 while the y-marginal ∝ e^{y²/2} is bimodal with C_P growing like e^{L²/2}
--   - encoding: 𝔼_ν[(∇²W)^{-1}], ‖·‖_op → entrywise Bochner integral of the matrix inverse, ℓ² operator norm via Matrix.toEuclideanCLM, value +∞ if some entry is not ν-integrable; reason: the expectation is finite exactly when every entry is integrable, and the proof of Proposition 4.2 (p. 30) uses this +∞ convention
--   - encoding: ν a probability measure with density e^{-W} on Ω, W ∈ C²(Ω) → W : ℝⁿ → ℝ with ContDiffOn ℝ 2 W Ω, ν = 1_Ω e^{-W} dx, ∫_Ω e^{-W} = 1 as a hypothesis; reason: same measures; values of W off Ω are irrelevant
--   - encoding: C_P(·), the best constant in (1.1) → the base `poincare` in ℝ≥0∞ (ambient locally Lipschitz tests on ℝⁿ, +∞ if no finite constant works); reason: same value whenever the constant is finite; +∞ otherwise
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 7, Proposition 1.2, (1.7); proof pp. 27–28. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
/-- Proposition 1.2, p. 7 (improved Brascamp–Lieb inequality, (1.7)). -/
theorem proposition_1_2 {n : ℕ} (Ω : Set (Space n)) (hΩ_open : IsOpen Ω)
    (hΩ_convex : Convex ℝ Ω) (W : Fn n) (hW : ContDiffOn ℝ 2 W Ω)
    (hW_norm : ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-W x)) = 1)
    (hW_pd : ∀ x ∈ Ω, (hessMatrix W x).PosDef) :
    poincare (domainLaw Ω W) ≤ avgInvHessNorm Ω W := by sorry
end UnconditionalKLS.Dunkl.Supplement
