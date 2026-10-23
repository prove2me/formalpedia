-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_conjugate_eq
-- name    : RiskFunctionals.Polyhedral.conjugate_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:36.719052+00:00
-- url     : https://prove2.me/theorems/4e63dbe5-032a-47a8-b481-affe5fb552b8
-- title:
--   Eq. (3.59) — the conjugate of a polyhedral functional is the concave indicator of the dual set
-- statement:
--   In the setting of Definition 3.37 ($T\ge1$, a filtration with trivial $\mathcal F_0$, $p\in[1,\infty)$, $1/p+1/q=1$), let the data satisfy conditions (i) and (ii). Then for every $Z\in\mathcal Z=\times_{t=1}^TL_q(\mathcal F_t)$ the conjugate (3.58) is
--   $$\mathcal R^+(Z)=\begin{cases}0,&Z\in\mathcal Z_*,\\-\infty,&\text{otherwise,}\end{cases}\tag{3.59}$$
--   with $\mathcal Z_*$ the dual set (3.56).
--
--   This identifies the dual set of the representation (3.55): substituting (3.59) into (3.57) yields Theorem 3.38's formula.
--
--   **Formalization Note** $\mathcal R^+$ is computed in `EReal`. The two cases are stated as two implications.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 162, Eq. (3.59) (proof of Theorem 3.38)

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 162,
Eq. (3.59), in the proof of Theorem 3.38. Under conditions (i) and (ii) of p. 159, the conjugate
(3.58) of the polyhedral functional (3.54) is the concave indicator of the dual set (3.56): for
every `Z ∈ 𝒵 = ×_{t=1}^T L_q(ℱ_t)`, `ℛ⁺(Z) = 0` if `Z ∈ 𝒵*` and `ℛ⁺(Z) = −∞` otherwise. -/
theorem conjugate_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    ∀ Z : ℕ → Ω → ℝ, IsAdaptedLp P q T 𝓕 Z →
      (Z ∈ D.dualSet P q T 𝓕 → D.conjugate P p T 𝓕 Z = 0) ∧
      (Z ∉ D.dualSet P q T 𝓕 → D.conjugate P p T 𝓕 Z = ⊥) := by sorry

end RiskFunctionals.Polyhedral
