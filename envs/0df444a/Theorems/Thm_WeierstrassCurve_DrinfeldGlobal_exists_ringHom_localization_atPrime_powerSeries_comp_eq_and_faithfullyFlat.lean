-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/164fa2d5-32b9-5a1e-b8e3-60b64758484a
-- title:
--   Faithful flatness of T[[X]] over the origin-chart local ring
-- statement:
--   Let $T$ be a commutative ring that is local, Noetherian and complete for the adic topology of its maximal ideal, and let $W$ be a Weierstrass curve over $T$. Write $\mathcal O$ for `OriginChartRing W`, the degree-zero homogeneous localisation `Away` of the graded quotient $T[X_0,X_1,X_2]/(W.\mathrm{polynomial})$ (with the grading induced from the homogeneous components of $T[X_0,X_1,X_2]$) at the image of the coordinate $X_1$; inside it sit the elements `xOverY W` and `zOverY W`, the degree-zero fractions $X_0/X_1$ and $X_2/X_1$. Let $\Phi : \mathcal O \to T[[X]]$ be a ring homomorphism such that: for every $t \in T$, $\Phi$ carries the image of $t$ under the canonical map from the degree-zero component to $\mathcal O$ to the constant series $t$; $\Phi(X_0/X_1) = -X$; and $\Phi(X_2/X_1) = -w$, where $w =$ `W.formalW` is the power series whose $n$-th coefficient is the $n$-th coefficient of the $n$-th iterate of the substitution `W.wSubst` started at $0$. Put $\mathfrak p = \Phi^{-1}(\mathfrak m_{T[[X]]})$. Then there exists a ring homomorphism $\psi$ from the localisation $\mathcal O_{\mathfrak p}$ to $T[[X]]$ whose composition with the localisation map $\mathcal O \to \mathcal O_{\mathfrak p}$ equals $\Phi$, and such that, for the $\mathcal O_{\mathfrak p}$-algebra structure on $T[[X]]$ given by $\psi$, the module $T[[X]]$ is faithfully flat over $\mathcal O_{\mathfrak p}$.
--
--   This identifies $T[[X]]$ as a faithfully flat extension of the local ring of the projective Weierstrass model at the origin, the formal parameter being supplied by the coordinate functions $X_0/X_1$ and $X_2/X_1$ together with the formal series $w$; in effect $T[[X]]$ is the completion of the Noetherian local ring $\mathcal O_{\mathfrak p}$. It is used to detect properties of sections through the origin from their formal expansions, and is cited in the comparison of the localisation map with $\Phi$ on the origin chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    ∃ ψ : Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))) →+* PowerSeries T,
      ψ.comp (algebraMap (OriginChartRing W) _) = Φ ∧
      (letI : Algebra (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T) :=
          ψ.toAlgebra;
        Module.FaithfullyFlat (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T)) := by sorry
