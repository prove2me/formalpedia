-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_theorem_4_6
-- name    : ViscosityPPDE.Comparison.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:07.21956+00:00
-- url     : https://prove2.me/theorems/a6acd007-304c-4d15-9f59-3818f3519cd6
-- title:
--   Theorem 4.6 — comparison principle for viscosity solutions of semilinear PPDEs; $u^0$ is the unique viscosity solution
-- statement:
--   Let $P_0$ be the Wiener measure on $\Omega$ and let $f, g$ satisfy Assumption 4.2 and $f$ Assumption 4.4. Consider the semilinear path-dependent PDE
--   $$-\partial_t u(t,\omega) - \tfrac12\operatorname{tr}\big(\partial^2_{\omega\omega}u(t,\omega)\big) - f\big(t,\omega,u(t,\omega),\partial_\omega u(t,\omega)\big) = 0,\qquad 0\le t<T,\ \omega\in\Omega.\qquad(3.1)$$
--
--   1. **Comparison.** Let $u^1$ be a viscosity subsolution and $u^2$ a viscosity supersolution of (3.1). If $u^1(T,\cdot)\le g\le u^2(T,\cdot)$, then $u^1\le u^2$ on $\Lambda$.
--   2. **Uniqueness.** Consequently, given the terminal condition $g$, $u^0$ of (4.3) is the unique viscosity solution of (3.1): $u^0$ is a viscosity solution with $u^0(T,\cdot) = g$, and every viscosity solution $u$ with $u(T,\cdot) = g$ equals $u^0$ on $\Lambda$.
--
--   This is the paper's main result: a comparison principle, and hence well-posedness, for the notion of viscosity solution of Definition 3.3, in which the tangency of test functions is tested by optimal stopping under the nonlinear expectation $\underline{\mathcal E}^L$.
--
--   **Formalization Note** The terminal inequalities hold for every $\omega$. The uniqueness part restates the printed "Consequently" sentence, including "$u^0$ is a viscosity solution", which the proof on p. 25 takes from Theorem 4.3. $u^0$ is any $u$ satisfying the BSDE characterisation `IsU0`, of which there is exactly one by Pardoux–Peng. Viscosity sub- and supersolutions each carry their own $L\ge 0$, one $L$ for all $(t,\omega)$.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Theorem 4.6, p. 16; proof p. 25

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem theorem_4_6 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (fhat : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ → Rd d → ℝ)
    (h44 : Assumption44 f fhat) :
    (∀ u1 u2 : ℝ≥0 → Omega d T 0 → ℝ, IsViscSub P0 f u1 → IsViscSuper P0 f u2 →
        (∀ ω, u1 T ω ≤ g ω) → (∀ ω, g ω ≤ u2 T ω) → ∀ t ω, t ≤ T → u1 t ω ≤ u2 t ω) ∧
      ∀ u0 : ℝ≥0 → Omega d T 0 → ℝ, IsU0 P0 f g u0 →
        IsViscSol P0 f u0 ∧ (∀ ω, u0 T ω = g ω) ∧
          ∀ u : ℝ≥0 → Omega d T 0 → ℝ, IsViscSol P0 f u → (∀ ω, u T ω = g ω) →
            ∀ t ω, t ≤ T → u t ω = u0 t ω := by sorry

end ViscosityPPDE.Comparison
