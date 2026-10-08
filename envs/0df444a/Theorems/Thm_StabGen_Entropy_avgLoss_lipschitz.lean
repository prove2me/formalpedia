-- Prove2me | Theorems.Thm_StabGen_Entropy_avgLoss_lipschitz
-- name    : StabGen.Entropy.avgLoss_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:11:41.089781+00:00
-- url     : https://prove2.me/theorems/02466c08-5a3d-48b4-8d18-35e2974b68fb
-- title:
--   The averaged loss (28) is $M$-Lipschitz for the $L^1$ norm
-- statement:
--   Let $\Theta$ carry a reference measure $\nu$ and let the base loss satisfy $0\le r(h_\theta,z)\le M$ for all $\theta$ and $z$, with $\theta\mapsto r(h_\theta,z)$ measurable. Let $\ell(g,z)=\int_\Theta r(h_\theta,z)g(\theta)\,d\theta$ be the averaged loss (28). For all integrable $g,g':\Theta\to\mathbb R$ and every example $z$,
--   $$|\ell(g,z)-\ell(g',z)|\le M\int_\Theta|g(\theta)-g'(\theta)|\,d\theta .$$
--
--   Since $\ell$ is linear in $g$, this is the statement that $\ell$ is $M$-admissible with respect to the class of densities; it is used twice in the proof of Theorem 24.
--
--   **Formalization Note** The page states the inequality for elements of $F$ (densities); it is stated here for all integrable $g,g'$, which contains that case. Integrability makes both Bochner integrals genuine.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 518, §5.2.3 (the display before Theorem 24)

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

namespace StabGen.Entropy

open MeasureTheory

/-- §5.2.3, p. 518: the averaged loss (28) is `M`-Lipschitz in `g` for the `L¹(ν)` norm,
`|ℓ(g, z) − ℓ(g', z)| ≤ M ∫_Θ |g(θ) − g'(θ)| dθ`, when the base loss `r` is bounded by `M`. -/
theorem avgLoss_lipschitz {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (g g' : Θ → ℝ) (hg : Integrable g ν) (hg' : Integrable g' ν) (z : Z) :
    |avgLoss ν r g z - avgLoss ν r g' z| ≤ M * ∫ θ, |g θ - g' θ| ∂ν := by sorry

end StabGen.Entropy
