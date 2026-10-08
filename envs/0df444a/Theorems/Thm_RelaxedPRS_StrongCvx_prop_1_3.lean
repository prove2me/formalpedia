-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_prop_1_3
-- name    : RelaxedPRS.StrongCvx.prop_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:40.983862+00:00
-- url     : https://prove2.me/theorems/30d62e07-627d-4464-a43e-2ea29f6c03cd
-- title:
--   Proposition 1.3 — lower fundamental inequality (1.17)
-- statement:
--   Let $z^*$ be a fixed point of the PRS map, $x^*=\operatorname{prox}_{\gamma g}(z^*)$, and $\gamma>0$. For points $a,b$ where $f,g$ respectively admit subgradients $u,v$, the lower fundamental inequality is
--   $$f(a)+g(b)-f(x^*)-g(x^*)\ge\gamma^{-1}\langle b-a,z^*-x^*\rangle+S_f(a,x^*)+S_g(b,x^*).$$
--   The second regularity term uses $b$, the point associated with $g$; the printed $S_g(x_f,x^*)$ is inconsistent with the proof and the theorem's use in (2.2). This bound supplies the lower half of the objective comparison.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 8, Proposition 1.3, (1.17), corrected second regularity argument

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace

namespace RelaxedPRS.StrongCvx

/-- Proposition 1.3, p. 8: the lower fundamental inequality (1.17), with
the printed `S_g(x_f,x*)` corrected to `S_g(x_g,x*)`. -/
theorem prop_1_3 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f)
    (hlg : 0 < βg → HasLipGrad βg g)
    (zs : H) (hzs : TPRS Pf Pg zs = zs)
    (a b u v : H)
    (hu : u ∈ MoreauProx.Characterization.subgrad f a)
    (hv : v ∈ MoreauProx.Characterization.subgrad g b) :
    let xs := xg Pg zs
    γ⁻¹ * ⟪b - a, zs - xs⟫_ℝ +
        auxS μf βf a xs u (gtF γ Pf Pg zs) +
        auxS μg βg b xs v (gtG γ Pg zs) ≤
      (f a).toReal + (g b).toReal - (f xs).toReal - (g xs).toReal := by sorry

end RelaxedPRS.StrongCvx
