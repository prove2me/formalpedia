-- Prove2me | Theorems.Thm_SKHessianAscent_theorem_4_2
-- name    : SKHessianAscent.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:11:19.532206+00:00
-- url     : https://prove2.me/theorems/07d62aca-11e3-4d3c-97f3-c645bdde2ad9
-- title:
--   Theorem 4.2, desideratum (d2a) — uniform local strong convexity of the TAP free energy along the localization path
-- statement:
--   Fix $0<\beta<1$ and a time horizon $T\ge0$. Let $A\sim\mathrm{GOE}(n)$, let $(y_t)_{t\ge0}$ be stochastic localization of the SK Gibbs measure $\mu_{\beta A}$ and $m_t=\langle\sigma\rangle_{y_t}$ its magnetization. Let $\mathcal S_{\beta,A}(c)=\{m\in(-1,1)^n:cD(m)\prec\nabla^2\mathcal F_{\mathrm{TAP}}(m)\}$ be the safe set and $B_\square(x,r)=\{u\in(-1,1)^n:\|u-x\|_2<r\}$.
--
--   There are constants $\rho=\rho(\beta,T)>0$ and $c_{\mathrm{TAP}}=c_{\mathrm{TAP}}(\beta,T)>0$, independent of $n$, such that
--
--   $$
--   \Pr_{A,B}\Big\{\forall t\in[0,T]:\ B_\square\big(m_t,\rho\sqrt n\big)\subseteq\mathcal S_{\beta,A}(c_{\mathrm{TAP}})\Big\}\ \ge\ 1-o_n(1).
--   $$
--
--   This is the desideratum that replaces global strong convexity of the TAP free energy, which fails for $0.798<\beta<1$: the free energy is strongly convex, relative to $D(m)$, in a ball of radius of order $\sqrt n$ around every point of the localization path.
--
--   **Formalization Note** The process is an `SLProcess` (posterior form $y_t=t\sigma+B_t$), and the statement holds on every probability space carrying one. "$1-o_n(1)$" is a sequence $\eta_n\to0$, chosen with $\rho$ and $c$ before $n$, bounding the outer probability of the complement of the event.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Theorem 4.2, p. 22; desideratum (d2a), p. 5

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Localization

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem theorem_4_2 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℝ≥0) :
    ∃ (ρ c : ℝ) (η : ℕ → ℝ), 0 < ρ ∧ 0 < c ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : SLProcess β n P),
        P {ω | ¬ ∀ t : ℝ≥0, t ≤ T →
            cubeBall (X.mag t ω) (ρ * Real.sqrt n) ⊆ safeSet β (X.mat ω) c} ≤
          ENNReal.ofReal (η n) := by sorry

end SKHessianAscent
