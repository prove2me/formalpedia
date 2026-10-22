-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_bonus_formula
-- name    : RelationalReciprocity.Dynamics.bonus_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:31.775688+00:00
-- url     : https://prove2.me/theorems/d2975f68-2e46-463d-bf86-755f2d689fbf
-- title:
--   Proof of Proposition 1, p. 44 — the bonus at the KKT point and its strict decrease in λ
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold. For a (DE) multiplier $\lambda\ge0$ write $e(\lambda),w(\lambda)$ for the positive-wage KKT effort and wage and $e_0(\lambda)=\sqrt{\theta/(1+\lambda)}$ for the zero-wage KKT effort. Then:
--
--   1. if $\eta^2\theta^3(1+\lambda)>1$, the binding-(IC) bonus is
--   $$
--   b\big(e(\lambda),w(\lambda)\big)=\frac{3\eta^2\theta^3(1+\lambda)-1}{6\eta^3\theta^3(1+\lambda)^3};
--   $$
--   2. at a zero wage, $b\big(e_0(\lambda),0\big)=\big(\sqrt{\theta/(1+\lambda)}\big)^3/3$;
--   3. the map $\lambda\mapsto b(e(\lambda),w(\lambda))$ is strictly decreasing on $\{\lambda\ge0:\eta^2\theta^3(1+\lambda)>1\}$, and $\lambda\mapsto b(e_0(\lambda),0)$ is strictly decreasing on $[0,\infty)$.
--
--   These formulas carry the wage and effort dynamics over to the bonus.
--
--   **Formalization Note.** The paper signs the derivatives $db_t/d(1+\lambda_{DE_t})<0$; the statement records the resulting strict monotonicity on each branch.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 44 (PDF 46), proof of Proposition 1

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Proof of Proposition 1, p. 44: at the KKT point of a multiplier `λ ≥ 0` the bonus equals
`(3η²θ³(1+λ) − 1)/(6η³θ³(1+λ)³)` on the positive-wage branch and `(√(θ/(1+λ)))³/3` on the
zero-wage branch, and on each branch it is strictly decreasing in `λ`. -/
theorem bonus_formula (P : Params) (hP : P.Standing) (hη : 0 < P.η) :
    (∀ lam : ℝ, 0 ≤ lam → 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam) →
      bonus P (kktEffort P lam) (kktWage P lam) =
        (3 * P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (6 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 3)) ∧
    (∀ lam : ℝ, 0 ≤ lam → bonus P (kktEffort0 P lam) 0 = kktEffort0 P lam ^ 3 / 3) ∧
    StrictAntiOn (fun lam => bonus P (kktEffort P lam) (kktWage P lam))
      {lam : ℝ | 0 ≤ lam ∧ 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam)} ∧
    StrictAntiOn (fun lam => bonus P (kktEffort0 P lam) 0) (Set.Ici 0) := by sorry

end RelationalReciprocity.Dynamics
