-- Prove2me | Theorems.Thm_ViscosityPPDE_Comparison_theorem_6_1
-- name    : ViscosityPPDE.Comparison.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:32:30.579985+00:00
-- url     : https://prove2.me/theorems/867d3853-e6ff-4368-9517-ee4f81727975
-- title:
--   Theorem 6.1 — the Perron envelopes coincide: $\underline u=\bar u$
-- statement:
--   Let $P_0$ be the Wiener measure and let Assumptions 4.2 and 4.4 hold. For $(t,\omega)\in\Lambda$ let $\overline{\mathcal D}(t,\omega)$, $\underline{\mathcal D}(t,\omega)$ be the classes (6.2), and
--   $$\bar u(t,\omega) = \inf\{\varphi(t,\mathbf 0):\varphi\in\overline{\mathcal D}(t,\omega)\},\qquad\underline u(t,\omega) = \sup\{\varphi(t,\mathbf 0):\varphi\in\underline{\mathcal D}(t,\omega)\}.\qquad(6.1)$$
--   Then
--   $$\underline u = \bar u\qquad(6.4)$$
--   on $\Lambda$: for every $(t,\omega)$ the set $\{\varphi(t,\mathbf 0):\varphi\in\overline{\mathcal D}(t,\omega)\}$ has a greatest lower bound, the set $\{\varphi(t,\mathbf 0):\varphi\in\underline{\mathcal D}(t,\omega)\}$ has a least upper bound, and the two are equal.
--
--   Combined with the partial comparison principle, this equality of the Perron envelopes is what yields the full comparison principle, Theorem 4.6.
--
--   **Formalization Note** No infimum or supremum is formed: the statement is that a single real number $v$ is the greatest lower bound of the first set and the least upper bound of the second, which in particular says both sets are nonempty and bounded on the relevant side. The statement does not mention $u^0$.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, Theorem 6.1, (6.4), p. 25

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Perron
import Definitions.Def_ViscosityPPDE_Comparison_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

theorem theorem_6_1 {d : ℕ} {T : ℝ≥0} (P0 : Measure (Omega d T 0))
    (hP0 : IsWiener P0) (f : ℝ≥0 → Omega d T 0 → ℝ → Rd d → ℝ) (g : Omega d T 0 → ℝ) (L0 : ℝ)
    (h42 : Assumption42 f g L0) (fhat : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ → Rd d → ℝ)
    (h44 : Assumption44 f fhat) (t : ℝ≥0) (ω : Omega d T 0) (ht : t ≤ T) :
    ∃ v : ℝ, IsGLB {x | ∃ φ, InDbar P0 f g t ω φ ∧ x = φ t (zeroPath d T t)} v ∧
      IsLUB {x | ∃ φ, InDlow P0 f g t ω φ ∧ x = φ t (zeroPath d T t)} v := by sorry

end ViscosityPPDE.Comparison
