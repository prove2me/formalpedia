-- Prove2me | Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
-- name    : WeierstrassCurve.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/faef1c26-3a96-57b3-8290-a21487b145e9
-- title:
--   Variable change series is an isomorphism of formal group laws
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $C$ a Weierstrass variable change over $R$, with unit $C.u$ and parameters $C.r, C.s, C.t$. Write $\psi =$ `W.variableChangeSeries C` for the one-variable power series $u\,(X - r\,w_W)\cdot\mathrm{invOfUnit}(1 + s(X - r\,w_W) + t\,w_W, 1)$, where $w_W =$ `W.formalW` is the series whose $n$-th coefficient is the $n$-th coefficient of `W.wIter n`; and write $F_W =$ `W.formalGroupLawFixed` for the two-variable series obtained by substituting `W.fgZ3Fixed` $= -X_0 - X_1 +$ `W.fgZ3NumFixed` $\cdot\,\mathrm{invOfUnit}($ `W.fgZ3Denom`$, 1)$ into `W.fgInv` $= -X\cdot \mathrm{invOfUnit}($ `W.fgInvDenom`$, 1)$. The theorem asserts two things simultaneously: first, the coefficient of $X^1$ in $\psi$ equals $u$; second, the substitution of $F_W$ into $\psi$ coincides with the substitution, into the corresponding series $F_{C\cdot W}$ attached to the transformed curve $C \bullet W$, of the pair of two-variable series obtained from $\psi$ by substituting $X_0$ and $X_1$ respectively. In classical notation, $\psi'(0) = u$ and $\psi(F_W(X_0,X_1)) = F_{C\cdot W}(\psi(X_0), \psi(X_1))$.
--
--   This is the statement that a change of Weierstrass coordinates induces an isomorphism of the associated one-dimensional formal group laws, with the change-of-parameter series $\psi_C$ as the isomorphism and $u$ as its leading coefficient. It is used to produce a formal group law homomorphism (indeed isomorphism) matching `variableChangeSeries`, and thence to transport formal parameters at the origin along isomorphisms of Weierstrass models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed.lean

import Definitions.Def_WeierstrassCurve_VariableChangeSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) ∧
      PowerSeries.subst W.formalGroupLawFixed (W.variableChangeSeries C) =
        MvPowerSeries.subst
          ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (W.variableChangeSeries C),
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (W.variableChangeSeries C)]
          (C • W).formalGroupLawFixed := by sorry
