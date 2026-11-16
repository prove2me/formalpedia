-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_prop_26
-- name    : TFIMPhaseDiagram.Classical.Supplement.prop_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:16.382244+00:00
-- url     : https://prove2.me/theorems/c7e37eeb-302b-40ea-bed2-24a1a5a8bc48
-- title:
--   Proposition 26 — Scalar derivative, positive magnetization and exact quadratic gap
-- statement:
--   Fix $b,\eta>0$ with $(b/\eta)\tanh\eta>1$. Write $R(r)=\sqrt{\eta^2+r^2}$ and $\phi(r)=\Phi_{b,\eta}(r1)$. For every real $r$,
--   $$\phi'(r)=r\left(\frac{\tanh R(r)}{R(r)}-\frac1b\right).$$
--   There is a unique $m_\ast\in(0,1)$ solving $\tanh R(bm_\ast)/R(bm_\ast)=1/b$, equivalently the positive stationary equation. With the exact printed constant
--   $$c_1=\frac{\eta((b/\eta)\tanh\eta-1)}8>0,$$
--   $$\phi(bm_\ast)-\phi(bm)\ge c_1(m-m_\ast)^2\qquad(m\ge0).$$
--   This identifies the magnetization used in the functional gap and the Curie–Weiss concentration theorem.
--
--   Differences from the source:
--   - encoding: the unique positive magnetization m∗ → a shared choice definition together with existence, uniqueness and membership conclusions; reason: all supporting results use the same source magnetization; no stationary equation is assumed as a hypothesis
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 16, Proposition 26

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Proposition 26, p.16; the numerical constant is exactly (26). -/
theorem prop_26 (b η : ℝ) (h : supercritical b η) :
    (∀ r : ℝ, HasDerivAt (scalarPhi b η)
      (r * (Real.tanh (radius η r) / radius η r - 1/b)) r) ∧
    (∃! m : ℝ, IsMagnetization b η m) ∧
    IsMagnetization b η (magnetization b η) ∧
    (deriv (scalarPhi b η) (b * magnetization b η) = 0 ↔
      Real.tanh (radius η (b * magnetization b η)) /
        radius η (b * magnetization b η) = 1/b) ∧
    0 < scalarGap b η ∧
    (∀ m : ℝ, 0 ≤ m → scalarGap b η * (m - magnetization b η)^2 ≤
      scalarPhi b η (b * magnetization b η) - scalarPhi b η (b*m)) := by sorry

end TFIMPhaseDiagram.Classical.Supplement
