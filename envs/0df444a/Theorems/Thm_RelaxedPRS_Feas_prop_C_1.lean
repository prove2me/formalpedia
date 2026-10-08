-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_prop_C_1
-- name    : RelaxedPRS.Feas.prop_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:42.819465+00:00
-- url     : https://prove2.me/theorems/217b8601-7d21-43f2-8aca-5885af5feac7
-- title:
--   Proposition C.1, p. 35 — the fixed-point set of T^{γ_f,γ_g}_PRS is C_f ∩ C_g
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\neq\emptyset$, let $\gamma_f,\gamma_g>0$, and let $P_f=\mathbf{prox}_{\gamma_f d^2_{C_f}}$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$. Then
--   $$
--   \{z\in\mathcal H : T^{\gamma_f,\gamma_g}_{\mathrm{PRS}}(z)=z\}=C_f\cap C_g,\qquad T^{\gamma_f,\gamma_g}_{\mathrm{PRS}}=\mathbf{refl}_{\gamma_f d^2_{C_f}}\circ\mathbf{refl}_{\gamma_g d^2_{C_g}} .
--   $$
--
--   In particular the fixed-point set does not depend on the step sizes, which is what allows them to vary from iteration to iteration in (5.1).
--
--   **Formalization Note** The nonempty intersection is the standing assumption of §5; without it the fixed-point set can be nonempty while $C_f\cap C_g=\emptyset$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 35, Proposition C.1

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proposition C.1, p. 35: for `γf, γg > 0` the set of fixed points of
`T^{γ_f,γ_g}_PRS = refl_{γ_f d²_{C_f}} ∘ refl_{γ_g d²_{C_g}}` is `C_f ∩ C_g`. -/
theorem prop_C_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (γf γg : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (Pf Pg : H → H)
    (hPf : IsProx γf (dsq Cf) Pf) (hPg : IsProx γg (dsq Cg) Pg) :
    {z : H | RelaxedPRS.StrongCvx.TPRS Pf Pg z = z} = Cf ∩ Cg := by sorry

end RelaxedPRS.Feas
