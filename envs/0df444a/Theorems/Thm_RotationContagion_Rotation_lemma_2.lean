-- Prove2me | Theorems.Thm_RotationContagion_Rotation_lemma_2
-- name    : RotationContagion.Rotation.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:32.079974+00:00
-- url     : https://prove2.me/theorems/cb3917ed-871d-4a49-91a3-7311c3c274f9
-- title:
--   Lemma 2 (corrected), p. 8 — exposure time has mean R/2 and a distribution symmetric around R/2
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$. Let $\mu$ be a probability measure on $[0,\infty)$, the law of the infection time $t^*$, and let the infected group $\omega$ be uniform on $\{0,1\}$ and independent of $t^*$. For a rotation schedule $r$, the exposure time $\tau = \int_{t^*}^{t^*+R} r(\omega,t)\,dt$ satisfies
--   $$\mathrm E\,\tau = \frac R2 \qquad\text{and}\qquad \Pr(\tau \le T) = \Pr(\tau \ge R - T) \ \text{ for every } T \in \mathbb R .$$
--
--   Symmetry of the distribution of $\tau$ around $R/2$ is what allows (P1) to be replaced by the relaxed problem (P2) over distributions of $\tau$ with mean $R/2$.
--
--   **Formalization Note** The page prints the symmetry as $F(\tau) = 1 - F(R-\tau)$ for the distribution function $F$. That identity fails at atoms: under the frequent rotation $\tau \equiv R/2$, so $F(R/2) = 1$ while $1 - F(R/2) = 0$. The page's proof establishes $\Pr(\tau \le T) = \Pr(\tau \ge R - T)$ and then writes $1 - F(R-T)$ for the right-hand side, which is $1 - F((R-T)^-)$. The statement here is the proof's own corrected identity, which is what "symmetric around $R/2$" means; it is stated for every real $T$. Probabilities are written as $\tfrac12\sum_\omega \mu(\{t^* : \ldots\})$.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 8, Lemma 2 and its proof

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

open MeasureTheory

/-- Lemma 2 (corrected), p. 8: the exposure time of the infected group has mean `R/2`, and its
distribution is symmetric around `R/2`: `Pr(τ ≤ T) = Pr(τ ≥ R - T)` for every `T`. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) :
    (1 / 2 : ℝ) * ∑ ω : Fin 2, ∫ t0, exposure P r ω t0 ∂μ = P.R / 2 ∧
      ∀ T : ℝ,
        (1 / 2 : ℝ) * ∑ ω : Fin 2, μ.real {t0 | exposure P r ω t0 ≤ T} =
          (1 / 2 : ℝ) * ∑ ω : Fin 2, μ.real {t0 | P.R - T ≤ exposure P r ω t0} := by sorry

end RotationContagion.Rotation
