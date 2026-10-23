-- Prove2me | Theorems.Thm_RiskFunctionals_Deviation_std_representation
-- name    : RiskFunctionals.Deviation.std_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:10.27121+00:00
-- url     : https://prove2.me/theorems/9334d5de-f62d-4260-ba82-a541e62e6e74
-- title:
--   Eq. (2.100) — $\mathbb{S}\mathrm{td}(Y)=\|Y-\mathbb EY\|_2=\sup\{\mathbb E(YZ) : \mathbb E(Z)=0,\ \mathbb E(Z^2)\le1\}$
-- statement:
--   Let $Y$ be a square integrable random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$, with standard deviation $\mathbb{S}\mathrm{td}(Y)=\sqrt{\mathbb{V}\mathrm{ar}(Y)}$. Then
--   $$\mathbb{S}\mathrm{td}(Y)=\|Y-\mathbb EY\|_2=\sup\{\mathbb E(YZ) : \mathbb E(Z)=0,\ \mathbb E(Z^2)\le1\}, \tag{2.100}$$
--   the supremum taken over square integrable $Z$.
--
--   This is the dual representation of the standard deviation, the case $p=2$ of the representation (2.99) of $\|Y-\mathbb EY\|_p$.
--
--   **Formalization Note** $\mathbb{S}\mathrm{td}(Y)$ is written as `Real.sqrt (variance Y P)` with Mathlib's variance, $\|\cdot\|_2$ as `eLpNorm · 2` converted to a real number. $Y$ and $Z$ are measurable and in $L_2$; the supremum is taken in the extended reals.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 101, Eq. (2.100)

import Mathlib

namespace RiskFunctionals.Deviation

open MeasureTheory ProbabilityTheory

/-- Eq. (2.100) (Pflug & Römisch, p. 101): for `Y ∈ L₂`, with `𝕊td(Y) = √𝕍ar(Y)`,
`𝕊td(Y) = ‖Y − 𝔼Y‖₂ = sup {𝔼(Y Z) : 𝔼(Z) = 0, 𝔼(Z²) ≤ 1}`, the supremum over `Z ∈ L₂`. -/
theorem std_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hY2 : MemLp Y 2 P) :
    Real.sqrt (variance Y P) = (eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂P) 2 P).toReal ∧
    ((Real.sqrt (variance Y P) : ℝ) : EReal) =
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z 2 P ∧ ∫ ω, Z ω ∂P = 0 ∧
          ∫ ω, Z ω ^ 2 ∂P ≤ 1},
        ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal) := by sorry

end RiskFunctionals.Deviation
