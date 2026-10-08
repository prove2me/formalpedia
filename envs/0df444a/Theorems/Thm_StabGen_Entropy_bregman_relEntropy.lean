-- Prove2me | Theorems.Thm_StabGen_Entropy_bregman_relEntropy
-- name    : StabGen.Entropy.bregman_relEntropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:12:15.535688+00:00
-- url     : https://prove2.me/theorems/61910a3f-d3d8-4322-a50f-2bacede91089
-- title:
--   The Bregman divergence of $K(\cdot,f_0)$ is $K$: $d_{K(\cdot,f_0)}(g,g')=K(g,g')$
-- statement:
--   Let $\nu$ be a σ-finite measure on $\Theta$ and let $f_0,g,g'$ be probability densities with respect to $\nu$, with $f_0>0$ and $g'>0$ everywhere, $K(g,f_0)<\infty$, $K(g',f_0)<\infty$, and $\theta\mapsto g(\theta)\ln(g'(\theta)/f_0(\theta))$ integrable. The gradient of $N=K(\cdot,f_0)$ at $g'$ is $\ln(g'/f_0)+1$, and the Bregman divergence $d_N(g,g')=N(g)-N(g')-\langle g-g',\nabla N(g')\rangle$ equals the relative entropy: $K(g,g')$ is finite and
--   $$K(g,g')=K(g,f_0)-K(g',f_0)-\int_\Theta\bigl(g(\theta)-g'(\theta)\bigr)\Bigl(\ln\frac{g'(\theta)}{f_0(\theta)}+1\Bigr)d\theta .$$
--
--   In the proof of Theorem 24 this identity turns the left side of Lemma 21 into the symmetrized relative entropy $K(f,f^{\setminus i})+K(f^{\setminus i},f)$, to which Pinsker's inequality applies.
--
--   **Formalization Note** The page asserts $d_{K(\cdot,f_0)}(g,g')=K(g,g')$ without conditions. The regularizer is not Fréchet differentiable on the set of densities, so the identity is stated with the explicit gradient $\ln(g'/f_0)+1$, at a point $g'>0$ where that expression is meaningful, under the finiteness and integrability conditions that make every integral genuine. The conclusion asserts finiteness of $K(g,g')$ together with the identity of real numbers.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 518, proof of Theorem 24 (Bregman divergence of the relative entropy); Bregman divergence defined in Appendix C, p. 525

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

namespace StabGen.Entropy

open MeasureTheory

/-- Proof of Theorem 24, p. 518: the Bregman divergence of `N = K(·, f0)` is the relative entropy,
`d_{K(·, f0)}(g, g') = K(g, g')`, written out with the gradient `∇K(·, f0)(g') = ln(g'/f0) + 1`:
for probability densities `g, g', f0` with `g', f0 > 0`, `K(g, f0), K(g', f0) < ∞` and
`g ln(g'/f0)` integrable, `K(g, g')` is finite and
`K(g, g') = K(g, f0) − K(g', f0) − ∫ (g − g')(ln(g'/f0) + 1) dν`. -/
theorem bregman_relEntropy {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SigmaFinite ν]
    (f0 g g' : Θ → ℝ) (hf0 : IsDensity ν f0) (hg : IsDensity ν g) (hg' : IsDensity ν g')
    (hf0_pos : ∀ θ, 0 < f0 θ) (hg'_pos : ∀ θ, 0 < g' θ)
    (hK : relEntropy ν g f0 ≠ ⊤) (hK' : relEntropy ν g' f0 ≠ ⊤)
    (hint : Integrable (fun θ => g θ * Real.log (g' θ / f0 θ)) ν) :
    relEntropy ν g g' ≠ ⊤ ∧
      (relEntropy ν g g').toReal =
        (relEntropy ν g f0).toReal - (relEntropy ν g' f0).toReal -
          ∫ θ, (g θ - g' θ) * (Real.log (g' θ / f0 θ) + 1) ∂ν := by sorry

end StabGen.Entropy
