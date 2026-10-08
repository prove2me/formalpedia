-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_proposition_5_4
-- name    : ViscosityPPDE.Comparison.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:31:56.841873+00:00
-- url     : https://prove2.me/theorems/baab9359-7e4e-4d9a-a53e-d86ee7cd60cf
-- title:
--   Proposition 5.4 — $u^0$ is uniformly continuous on $\Lambda$ under $d_\infty$
-- statement:
--   Let $P_0$ be the Wiener measure on $\Omega$, and let $f,g$ satisfy Assumption 4.2. Let $u^0$ be the function of (4.3), $u^0(t,\omega) = Y^{0,t,\omega}_t$ for the solution of the BSDE (4.2). Then $u^0$ is uniformly continuous in $\Lambda$ under $d_\infty$: for every $\varepsilon>0$ there is $\delta>0$ such that for all $(t,\omega),(t',\omega')\in\Lambda$,
--   $$d_\infty\big((t,\omega),(t',\omega')\big) < \delta \implies |u^0(t,\omega) - u^0(t',\omega')| < \varepsilon.$$
--
--   This is the regularity half of the existence result Theorem 4.3: it puts $u^0$ in the class $C^0$ in which viscosity solutions are sought.
--
--   **Formalization Note** $u^0$ is any $u$ satisfying the BSDE characterisation `IsU0`; exactly one $u$ does, by Pardoux–Peng. Assumption 4.2 is a structure on the pair $(f,g)$.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Proposition 5.4, p. 19

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem proposition_5_4 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (u : ℝ≥0 → Omega d T 0 → ℝ) (hu : IsU0 P0 f g u) :
    ∀ ε > 0, ∃ δ > 0, ∀ (t t' : ℝ≥0) (ω ω' : Omega d T 0), t ≤ T → t' ≤ T →
      DInfLt T t ω.1 t' ω'.1 δ → |u t ω - u t' ω'| < ε := by sorry

end ViscosityPPDE.Comparison
