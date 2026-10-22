-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_fenchel_moreau_step
-- name    : RiskFunctionals.Polyhedral.fenchel_moreau_step
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:57.977988+00:00
-- url     : https://prove2.me/theorems/553442f8-e24b-49a9-9a4b-1ecbf34ae41c
-- title:
--   Eqs. (3.57)–(3.58) — the Fenchel–Moreau representation of a polyhedral functional through its conjugate
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $T\ge1$, $\boldsymbol{\mathcal F}=(\mathcal F_0,\dots,\mathcal F_T)$ a filtration with $\mathcal F_0$ trivial, $p\in[1,\infty)$ and $1/p+1/q=1$. Let $\mathcal R$ be a polyhedral functional (3.54) whose data satisfy condition (i) (polyhedral cones, complete recourse) and condition (ii) (dual feasibility). Then for every $Y\in\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$
--   $$\mathcal R(Y)=\inf\Bigl\{\sum_{t=1}^T\mathbb E(Y_tZ_t)-\mathcal R^+(Z):\ Z\in\mathcal Z\Bigr\},\qquad \mathcal Z=\times_{t=1}^TL_q(\mathcal F_t),\tag{3.57}$$
--   where $\mathcal R^+(Z)=\inf\{\sum_{t=1}^T\mathbb E(Y_tZ_t)-\mathcal R(Y):Y\in\mathcal Y\}$ is the conjugate (3.58).
--
--   This is the Fenchel–Moreau–Rockafellar step in the proof of Theorem 3.38; together with the computation (3.59) of the conjugate it gives the dual representation (3.55).
--
--   **Formalization Note** Infima are taken in `EReal`, where $r-(-\infty)=+\infty$, so a $Z$ with $\mathcal R^+(Z)=-\infty$ contributes $+\infty$ and does not affect the infimum. $\mathcal Z$ consists of processes with $Z_t$ $\mathcal F_t$-measurable and in $L_q$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 161, Eqs. (3.57)–(3.58) (proof of Theorem 3.38)

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 161,
Eqs. (3.57)–(3.58), in the proof of Theorem 3.38. Under conditions (i) and (ii) of p. 159, the
polyhedral functional `ℛ` of (3.54) satisfies, for every `Y ∈ 𝒴 = ×_{t=1}^T L_p(ℱ_t)`,
`ℛ(Y) = inf{Σ_{t=1}^T 𝔼(Y_t Z_t) − ℛ⁺(Z) : Z ∈ 𝒵}` (3.57), where `𝒵 = ×_{t=1}^T L_q(ℱ_t)`,
`1/p + 1/q = 1`, and `ℛ⁺` is the conjugate (3.58). -/
theorem fenchel_moreau_step {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y =
        sInf {x : EReal | ∃ Z : ℕ → Ω → ℝ, IsAdaptedLp P q T 𝓕 Z ∧
          x = (pairing P T Y Z : EReal) - D.conjugate P p T 𝓕 Z} := by sorry

end RiskFunctionals.Polyhedral
