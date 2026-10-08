-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_eq_6_3
-- name    : ViscosityPPDE.Comparison.eq_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:00.128015+00:00
-- url     : https://prove2.me/theorems/159022c7-c89e-4ecf-adde-4640b48380c4
-- title:
--   (6.3) — $\underline u\le u^0\le\bar u$
-- statement:
--   Let $P_0$ be the Wiener measure and let Assumption 4.2 hold. Let $u^0$ be the function of (4.3) and, for $(t,\omega)\in\Lambda$, let $\overline{\mathcal D}(t,\omega)$ and $\underline{\mathcal D}(t,\omega)$ be the classes (6.2). Then for every $(t,\omega)\in\Lambda$,
--   $$\varphi(t,\mathbf 0)\le u^0(t,\omega)\ \text{ for all }\varphi\in\underline{\mathcal D}(t,\omega),\qquad u^0(t,\omega)\le\varphi(t,\mathbf 0)\ \text{ for all }\varphi\in\overline{\mathcal D}(t,\omega).$$
--   With $\bar u(t,\omega) = \inf\{\varphi(t,\mathbf 0) : \varphi\in\overline{\mathcal D}(t,\omega)\}$ and $\underline u(t,\omega) = \sup\{\varphi(t,\mathbf 0):\varphi\in\underline{\mathcal D}(t,\omega)\}$ (6.1), this is $\underline u\le u^0\le\bar u$.
--
--   It places the BSDE value between the two Perron envelopes; Theorem 6.1 then closes the gap.
--
--   **Formalization Note** The envelopes are not formed; the statement is the equivalent family of inequalities. $\overline{\mathcal D}(t,\omega)$ is nonempty (it contains $\varphi_s = \sup g + (T-s)\sup|f|$), and so is $\underline{\mathcal D}(t,\omega)$, so this is exactly $\underline u\le u^0\le\bar u$. $u^0$ is any $u$ satisfying `IsU0`.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, (6.1)–(6.3), p. 25

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem eq_6_3 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (u : ℝ≥0 → Omega d T 0 → ℝ) (hu : IsU0 P0 f g u)
    (t : ℝ≥0) (ω : Omega d T 0) (ht : t ≤ T) :
    (∀ φ, InDlow P0 f g t ω φ → φ t (zeroPath d T t) ≤ u t ω) ∧
      (∀ φ, InDbar P0 f g t ω φ → u t ω ≤ φ t (zeroPath d T t)) := by sorry

end ViscosityPPDE.Comparison
