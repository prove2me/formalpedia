-- Prove2me | Theorems.Thm_StabGen_Entropy_pinsker_L1
-- name    : StabGen.Entropy.pinsker_L1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:12:05.161983+00:00
-- url     : https://prove2.me/theorems/02a4f271-306c-44b0-a480-c2bd2b974be9
-- title:
--   Pinsker's inequality: $\frac12\left(\int|g-g'|\right)^2\le K(g,g')$
-- statement:
--   Let $\nu$ be a σ-finite measure on $\Theta$ and let $g,g'$ be probability densities with respect to $\nu$. Then
--   $$\frac12\left(\int_\Theta|g(\theta)-g'(\theta)|\,d\theta\right)^2\le K(g,g'),$$
--   where $K(g,g')\in[0,\infty]$ is the relative entropy (Kullback–Leibler divergence) of $g\,\nu$ from $g'\,\nu$.
--
--   This is Pinsker's inequality in its $L^1$ form, quoted in the proof of Theorem 24 to convert a bound on relative entropies into a bound on the $L^1$ distance between two posteriors.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$, the left side entering through `ENNReal.ofReal`, so no finiteness hypothesis on $K$ is needed (when $K=\infty$ it holds trivially). The page says "for any $g, g'$"; they are taken in the class $F$ of probability densities, the only setting in which $K$ is defined in §5.2.3.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 518, proof of Theorem 24 (property of the relative entropy, citing Cover and Thomas 1991)

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

namespace StabGen.Entropy

open MeasureTheory

/-- Proof of Theorem 24, p. 518 (Pinsker's inequality, `L¹` form): for probability densities
`g, g'` with respect to `ν`, `½ (∫_Θ |g(θ) − g'(θ)| dθ)² ≤ K(g, g')`, in `[0, ∞]`. -/
theorem pinsker_L1 {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SigmaFinite ν]
    (g g' : Θ → ℝ) (hg : IsDensity ν g) (hg' : IsDensity ν g') :
    ENNReal.ofReal ((1 / 2) * (∫ θ, |g θ - g' θ| ∂ν) ^ 2) ≤ relEntropy ν g g' := by sorry

end StabGen.Entropy
