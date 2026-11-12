-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_linearized_gradient_law
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.linearized_gradient_law
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:25:36.292976+00:00
-- url     : https://prove2.me/theorems/b974a52e-8965-46e8-9042-88d5566777ca
-- title:
--   First-order QNTK gradient-descent evolution
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Let $A$ be a finite training subset, $I$ a finite observable family, $y_b$ real labels, $\epsilon_b=z_b-y_b$, and $\eta>0$. Use the unaveraged loss $\frac12\sum_{b\in A\times I}\epsilon_b^2$. For the real gradient step $\Delta\theta_\ell=-\eta\sum_b\epsilon_b\partial_\ell z_b$, its first Taylor output increment satisfies
--   $$
--   \sum_\ell\partial_\ell z_a\,\Delta\theta_\ell=-\eta\sum_{b\in A\times I}K_{ab}\epsilon_b.
--   $$
--   For complex amplitude outputs, duplicate residuals and outputs into conjugate pairs, and form the complex Gram kernel $\mathcal K$ of the doubled real-parameter derivatives. The analogous real gradient of $\frac12\sum|z-y|^2$ gives $\Delta^{(1)}\mathcal z_\mu=-(\eta/2)\sum_{\nu\in A\times\{0,1\}\times H}\mathcal K_{\mu\nu}\mathcal\epsilon_\nu$. The scalar formula is the singleton-data, singleton-observable case. These identities describe first Taylor increments and provide the evolution laws used in the frozen models.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 2, Eq.(4); Eqs.(25)-(28); SM Eqs.(132)-(140)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF pp.2,5,23 Eqs.(4),(25)-(28),(88)-(93), and pp.28-29 Eqs.(132)-(140).
This is the first Taylor increment induced by the real gradient of the unaveraged squared
loss. It is not equality with an exact nonlinear one-step circuit increment. Unit data and
Unit observables recover the scalar optimization law. -/
theorem linearized_gradient_law {D T I : Type*} [Fintype T] [Fintype I]
    {h L : ℕ} (M : ExpectationNetwork D I h L) (embed : T ↪ D)
    (theta : Fin L → ℝ) (y : T × I → ℝ) (eta : ℝ) (heta : 0 < eta) :
    (let e := fun b : T × I => expectationOutput M theta (trainingIndex embed b) - y b
     let dp := fun l => -eta * ∑ b, e b *
       coordinateDerivative (fun u => expectationOutput M u (trainingIndex embed b)) theta l
     ∀ a, (∑ l, coordinateDerivative (fun u => expectationOutput M u a) theta l * dp l) =
       -eta * ∑ b, expectationKernel M theta a (trainingIndex embed b) * e b) ∧
    (∀ (N : AmplitudeModel D h L) (labels : T × Fin h → ℂ),
      let e := fun b : T × Fin h => basisAmplitude N theta (embed b.1, b.2) - labels b
      let dp := fun l => -eta * (∑ b, e b *
        star (coordinateDerivative (fun u => basisAmplitude N u (embed b.1, b.2)) theta l)).re
      let de := fun b : T × Bool × Fin h =>
        if b.2.1 then star (e (b.1, b.2.2)) else e (b.1, b.2.2)
      ∀ a, (∑ l, coordinateDerivative (fun u => doubledAmplitude N u a) theta l * (dp l : ℂ)) =
        -(eta / 2 : ℝ) • (∑ b : T × Bool × Fin h,
          amplitudeKernel N theta a (embed b.1, b.2.1, b.2.2) * de b)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
