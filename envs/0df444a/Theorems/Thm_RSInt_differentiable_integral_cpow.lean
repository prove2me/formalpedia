-- Prove2me | Theorems.Thm_RSInt_differentiable_integral_cpow
-- name    : RSInt.differentiable_integral_cpow
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:54:45.655768+00:00
-- url     : https://prove2.me/theorems/93bdd6fa-64cc-4612-89de-2548c73cede8
-- title:
--   Differentiation under a Gaussian-dominated complex-power integral
-- statement:
--   Let $W,X:\mathbb R\to\mathbb C$ be continuous, with $X(v)$ in the complex
--   plane cut along the nonpositive real axis for every $v$. Assume there are real
--   constants $m,\alpha,\beta,C,a,b$ with $m>0$ and $a>0$ such that
--
--   $$m\le |X(v)|\le\alpha+\beta|v|\quad(v\in\mathbb R),\qquad
--   |W(v)|\le C e^{-av^2+b|v|}\quad(|v|\ge1).$$
--
--   Then the following function of the complex variable $s$ is complex differentiable
--   on all of $\mathbb C$:
--
--   $$s\longmapsto\int_{\mathbb R}W(v)X(v)^s\,dv,$$
--
--   where the principal complex power is used.
--
--   This supplies analytic dependence on the exponent in the contour integral.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Entire.lean#L49-L162

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/

theorem RSInt.differentiable_integral_cpow {W X : ℝ → ℂ} (hW : Continuous W) (hX : Continuous X)
    (hXs : ∀ v, X v ∈ slitPlane) {m : ℝ} (hm : 0 < m) (hXm : ∀ v, m ≤ ‖X v‖)
    {α β : ℝ} (hXb : ∀ v, ‖X v‖ ≤ α + β * |v|)
    {C a b : ℝ} (ha : 0 < a) (hWb : ∀ v, 1 ≤ |v| → ‖W v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Differentiable ℂ (fun s : ℂ => ∫ v : ℝ, W v * X v ^ s) := by sorry
