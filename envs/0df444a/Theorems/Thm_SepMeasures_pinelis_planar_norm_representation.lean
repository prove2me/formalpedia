-- Prove2me | Theorems.Thm_SepMeasures_pinelis_planar_norm_representation
-- name    : SepMeasures.pinelis_planar_norm_representation
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:44.355407+00:00
-- url     : https://prove2.me/theorems/53a2fe47-a0df-4c4a-b3ff-c9fba559059b
-- title:
--   §3.3 display, p.25 ([Pin16, Theorem 1.1]) — every norm on $\mathbb R^2$ is $\|z\|=\int|a\cdot z|\,\rho(da)$ for a finite $\rho$
-- statement:
--   For every norm $\|\cdot\|$ on $\mathbb R^2$ there is a finite non-negative Borel measure $\rho$ on $A=\mathbb R^2\setminus\{0\}$ such that
--   $$\|z\|=\int_A|a\cdot z|\,\rho(da)\qquad(z\in\mathbb R^2).$$
--
--   The paper quotes this from Pinelis [Pin16, Theorem 1.1]. It turns distances into integrals of separation indicators of lines, which is how the probability inequality (8) becomes the distance inequality $\sum_iC(H_i)\ge L$ in Theorem 3.3.
--
--   Differences from the source:
--   - encoding: a finite non-negative Borel measure ρ on A = ℝ² ∖ {0} → a finite measure ρ on ℝ² with ρ {0} = 0; reason: the same measures
--   - encoding: ‖z‖ = ∫_A |a · z| ρ(da) → ENNReal.ofReal (N z) = ∫⁻ a, ENNReal.ofReal |⟪a, z⟫| ∂ρ; reason: a lower Lebesgue integral of a non-negative function; the equality forces it to be finite, so it equals the Bochner integral
--   - encoding: a norm ‖·‖ on ℝ² → N : Seminorm ℝ (EuclideanSpace ℝ (Fin 2)) with N x = 0 → x = 0; a · z the Euclidean inner product; reason: a definite seminorm is exactly a norm; the Euclidean structure of EuclideanSpace is used only for hyperplane equations, Lebesgue measure, balls and dist(x, H), as in the paper
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §3.3, display on p.25 (quoting [Pin16, Theorem 1.1])

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), §3.3, display on p.25, quoting [Pin16, Theorem 1.1]:
for every norm `‖·‖` on `ℝ²` there is a finite non-negative Borel measure `ρ` on
`A = ℝ² ∖ {0}` such that `‖z‖ = ∫_A |a · z| ρ(da)` for all `z ∈ ℝ²`.

**Formalization Note.** `ρ` is a finite measure on `ℝ²` with `ρ {0} = 0` (a finite measure on
`ℝ² ∖ {0}`). The integral is a lower Lebesgue integral of `|⟨a, z⟩|` in `ℝ≥0∞`, compared with
`‖z‖` cast to `ℝ≥0∞`; no integrability side condition is involved. -/
theorem pinelis_planar_norm_representation (N : Seminorm ℝ (E 2)) (hN : ∀ x, N x = 0 → x = 0) :
    ∃ ρ : Measure (E 2), IsFiniteMeasure ρ ∧ ρ {0} = 0 ∧
      ∀ z : E 2, ENNReal.ofReal (N z) = ∫⁻ a, ENNReal.ofReal |inner ℝ a z| ∂ρ := by sorry

end SepMeasures
