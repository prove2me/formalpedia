-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_eq_66
-- name    : PoissonDirichlet.Wendel.eq_66
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:50.147979+00:00
-- url     : https://prove2.me/theorems/f4caae98-b774-42be-a2d8-707c9daf8a7a
-- title:
--   (66), p. 871 — under PD(α, 0), A_1 = V_1/V_2 has density α x^{−α−1} on (1, ∞)
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution. Then $A_1=V_1/V_2$ satisfies
--   $$P(A_1\in dx)=\alpha x^{-\alpha-1}\,dx\,1(x>1).$$
--
--   This is the law whose Laplace transform is $\phi_\alpha$, the building block of part (i) of Proposition 11.
--
--   **Formalization Note** The paper writes $A_1:=\Delta_1/\Delta_2$ in the Poisson representation; here $A_1$ is the PD-side variable $V_1/V_2$ of (31), which equals $\Delta_1/\Delta_2$ under (26). The density is with respect to Lebesgue measure.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 871, (66)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- (66), p. 871: for `V` with law PD(α, 0), 0 < α < 1, `A_1 = V_1 / V_2` has density
`α x^{-α-1}` on (1, ∞). 0-based: `Aseq (V ω) 1 = V ω 0 / V ω 1`. -/
theorem eq_66 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) :
    HasLaw (fun ω => Aseq (V ω) 1) (tailLaw α) P := by sorry

end PoissonDirichlet.Wendel
