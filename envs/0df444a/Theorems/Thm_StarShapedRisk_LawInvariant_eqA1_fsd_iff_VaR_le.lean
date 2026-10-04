-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_eqA1_fsd_iff_VaR_le
-- name    : StarShapedRisk.LawInvariant.eqA1_fsd_iff_VaR_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:10:12.224289+00:00
-- url     : https://prove2.me/theorems/ac241b73-c164-4a2e-ac51-a85e9154e89b
-- title:
--   Eq. (A.1) — first-order dominance of losses is the pointwise VaR order
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$ and let $X,Y$ be bounded measurable losses with distribution functions $F_X(x)=P(X\le x)$ and $F_Y(x)=P(Y\le x)$. Then
--   $$F_X(x)\ge F_Y(x)\ \text{ for all }x\in\mathbb R\quad\Longleftrightarrow\quad \mathrm{VaR}_\alpha(X)\le\mathrm{VaR}_\alpha(Y)\ \text{ for all }\alpha\in(0,1).$$
--   Either condition is what the paper denotes $X\succsim_{\mathrm{FSD}}Y$: $X$ is the stochastically smaller loss.
--
--   This equivalence turns first-order dominance into a family of scalar inequalities, which is how the proof of Theorem 5 computes $\inf\{m\mid X-m\succsim_{\mathrm{FSD}}Y\}=\sup_{\alpha\in(0,1)}\{\mathrm{VaR}_\alpha(X)-\mathrm{VaR}_\alpha(Y)\}$.
--
--   **Formalization Note** No atomlessness is assumed; the equivalence holds on every probability space. Levels are restricted to the open interval $(0,1)$ as on the page.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2652, Appendix, proof of Theorem 5, Eq. (A.1)

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Eq. (A.1) (p. 2652): for bounded measurable losses `X`, `Y` on a
probability space, `F_X ≥ F_Y` pointwise if and only if `VaR_α(X) ≤ VaR_α(Y)` for all
`α ∈ (0,1)`. No atomlessness is assumed. -/
theorem eqA1_fsd_iff_VaR_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Positions Ω) :
    FSD P X.1 Y.1 ↔ ∀ α ∈ Set.Ioo (0 : ℝ) 1, VaR P α X.1 ≤ VaR P α Y.1 := by sorry

end StarShapedRisk.LawInvariant
