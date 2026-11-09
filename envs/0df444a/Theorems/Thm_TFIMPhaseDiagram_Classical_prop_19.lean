-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_19
-- name    : TFIMPhaseDiagram.Classical.prop_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:33.674522+00:00
-- url     : https://prove2.me/theorems/c17d0ba6-8032-45d8-8a1f-d952f6ed9cd6
-- title:
--   Proposition 19 — Positive two-spin representation and sharp tilt supremum
-- statement:
--   For every strictly positive table $r:\{\pm1\}^2\to\mathbb R_{>0}$, let $J,v_1,v_2$ be its quarter-log odds parameters and $C=(\prod_s r(s))^{1/4}$. These are the unique parameters with $C>0$ representing the table:
--   $$r(s)=C\exp(Js_1s_2+v_1s_1+v_2s_2),\qquad |\tanh J|=\sup_{w\in\mathbb R^2}|\operatorname{Cov}(T_wr)_{1,2}|.$$
--   Both signs of $J$ are allowed. The sharp tilt supremum links effective two-spin interactions to absolute covariance bounds.
--
--   Differences from the source:
--   - encoding: positive two-spin table and unique Ising parameters → Bool pairs, positive scale, explicit log parameters and a real supremum; reason: The positivity of the scale follows from the representation of a positive table; the supremum is nonempty and bounded by 1.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.12 = PDF p.12, Proposition 19

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 19, p.12: representation, uniqueness, and the sharp all-tilt supremum. -/
theorem prop_19 (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) :
  (∀ s, r s = pairC r * Real.exp (pairJ r * spin s.1 * spin s.2 +
    pairV1 r * spin s.1 + pairV2 r * spin s.2)) ∧
  (∀ (C J v1 v2 : ℝ), 0 < C →
    (∀ s : Bool × Bool, r s = C * Real.exp (J * spin s.1 * spin s.2 + v1*spin s.1 + v2*spin s.2)) →
    C = pairC r ∧ J = pairJ r ∧ v1 = pairV1 r ∧ v2 = pairV2 r) ∧
  |Real.tanh (pairJ r)| = sSup (Set.range (fun w : ℝ × ℝ => |pairCov r w|)) := by sorry
end TFIMPhaseDiagram.Classical
