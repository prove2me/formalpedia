-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_polyhedral_dual_representation
-- name    : RiskFunctionals.Polyhedral.polyhedral_dual_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:55:06.751385+00:00
-- url     : https://prove2.me/theorems/a92c8812-e616-48a6-9c89-374acf279cc0
-- title:
--   Theorem 3.38 — polyhedral multi-period functionals are finite, concave, continuous, information monotone, and dual to the polyhedral set (3.56)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $T\ge1$, $\boldsymbol{\mathcal F}=(\mathcal F_0,\dots,\mathcal F_T)$ a filtration in $\mathcal F$ with $\mathcal F_0=\{\emptyset,\Omega\}$, $p\in[1,\infty)$ and $q\in(1,\infty]$ with $1/p+1/q=1$. Let $\mathcal R$ be the polyhedral functional
--   $$\mathcal R(Y)=\sup\Bigl\{\sum_{t=0}^T\mathbb E(\langle c_t,v_t\rangle)\ :\ v_t\in L_p(\mathcal F_t;\mathbb R^{k_t}),\ v_t\in V_t,\ t=0,\dots,T;\ \sum_{\tau=0}^t\langle w_{t,\tau},v_{t-\tau}\rangle=Y_t,\ t=1,\dots,T\Bigr\}\tag{3.54}$$
--   on $\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$, with non-empty polyhedral $V_t$, and assume (i) every $V_t$ is a polyhedral cone and $\langle w_{t,0},V_t\rangle=\mathbb R$, $t=1,\dots,T$; (ii) there is $\bar u\in\mathbb R^T$ with $c_0-\sum_{\tau=1}^Tw_{\tau,\tau}\bar u_\tau\in V_0^*$ and $c_t-\sum_{\tau=t}^Tw_{\tau,\tau-t}\bar u_\tau\in V_t^*$, $t=1,\dots,T$. Then:
--   1. $\mathcal R$ is finite on $\mathcal Y$;
--   2. $\mathcal R$ is positively homogeneous, concave and continuous on $\mathcal Y$;
--   3. $\mathcal R$ satisfies (MA0): if $\boldsymbol{\mathcal F}'$ is another such filtration with $\mathcal F_t\subseteq\mathcal F'_t$ for all $t$, then $\mathcal R(Y;\boldsymbol{\mathcal F})\le\mathcal R(Y;\boldsymbol{\mathcal F}')$ for $Y$ adapted to $\boldsymbol{\mathcal F}$;
--   4. for every $Y\in\mathcal Y$,
--   $$\mathcal R(Y)=\inf\Bigl\{\sum_{t=1}^T\mathbb E(Y_tZ_t):Z\in\mathcal Z_*\Bigr\},\tag{3.55}$$
--   $$\mathcal Z_*=\Bigl\{Z\in\times_{t=1}^TL_q(\mathcal F_t):\ c_0-\sum_{\tau=1}^Tw_{\tau,\tau}\mathbb E(Z_\tau)\in V_0^*,\ c_t-\sum_{\tau=t}^Tw_{\tau,\tau-t}\mathbb E(Z_\tau\mid\mathcal F_t)\in V_t^*,\ t=1,\dots,T\Bigr\}.\tag{3.56}$$
--
--   This is the duality theorem for polyhedral multi-period acceptability functionals: the functional, defined as the value of a linear multi-stage stochastic program, is the lower envelope of linear functionals over a dual set described by finitely many (conditional) linear constraints.
--
--   **Formalization Note** $\mathcal R$ takes values in `EReal`; finiteness is the first conclusion and the other properties are stated for its real part. The infimum (3.55) is taken in `EReal` over $\mathcal Z_*$. Coefficients are stored as `W t s` $=w_{t,t-s}$ (see the definition). Constraints with random variables hold almost surely; conditional expectations are Mathlib's. (MA0) is stated for every pair of filtrations $\boldsymbol{\mathcal F}\subseteq\boldsymbol{\mathcal F}'$ with the same data. Continuity is the $\varepsilon$–$\delta$ form for the norms $\|Y_t\|_p$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 160, Theorem 3.38

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 160,
Theorem 3.38. If conditions (i) (polyhedral cones, complete recourse) and (ii) (dual
feasibility) of p. 159 hold and `ℛ` is the polyhedral functional (3.54), then `ℛ` is finite,
positively homogeneous, concave and continuous on `𝒴 = ×_{t=1}^T L_p(ℱ_t)`, satisfies (MA0),
and admits the representation (3.55) `ℛ(Y) = inf{Σ_{t=1}^T 𝔼(Y_t Z_t) : Z ∈ 𝒵*}` with `𝒵*`
the subset (3.56) of `𝒵 = ×_{t=1}^T L_q(ℱ_t)`, `1/p + 1/q = 1`. -/
theorem polyhedral_dual_representation {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T) (hii : D.DualFeasible T) :
    (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
    PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
    InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
    (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
      D.functional P p T 𝓕 Y =
        sInf {x : EReal | ∃ Z ∈ D.dualSet P q T 𝓕, x = (pairing P T Y Z : EReal)}) := by sorry

end RiskFunctionals.Polyhedral
