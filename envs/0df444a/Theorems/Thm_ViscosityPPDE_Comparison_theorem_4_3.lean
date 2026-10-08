-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_theorem_4_3
-- name    : ViscosityPPDE.Comparison.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:10.047248+00:00
-- url     : https://prove2.me/theorems/cc0951ce-57de-422b-a6ea-e604aec4edac
-- title:
--   Theorem 4.3 — $u^0$ is a viscosity solution of the PPDE with terminal condition $g$
-- statement:
--   Let $P_0$ be the Wiener measure and let $f,g$ satisfy Assumption 4.2. Then $u^0$ of (4.3) is a viscosity solution of the PPDE (3.1)
--   $$-\partial_t u - \tfrac12\operatorname{tr}(\partial^2_{\omega\omega}u) - f(t,\omega,u,\partial_\omega u) = 0,\qquad 0\le t<T,$$
--   with terminal condition $g$: it is a viscosity subsolution and a viscosity supersolution in the sense of Definition 3.3, and $u^0(T,\omega) = g(\omega)$ for every $\omega\in\Omega$.
--
--   This is the existence half of the well-posedness theory: the path-dependent nonlinear Feynman–Kac formula, saying that the BSDE value is a viscosity solution.
--
--   **Formalization Note** $u^0$ is any $u$ satisfying `IsU0` (exactly one does). "With terminal condition $g$" is the clause $u^0(T,\cdot) = g$; it follows from (4.2) at $t = T$, since $\Omega^T$ consists of the zero path only. Assumption 4.4 is not assumed.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Theorem 4.3, p. 16

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem theorem_4_3 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (u : ℝ≥0 → Omega d T 0 → ℝ) (hu : IsU0 P0 f g u) :
    IsViscSol P0 f u ∧ ∀ ω, u T ω = g ω := by sorry

end ViscosityPPDE.Comparison
