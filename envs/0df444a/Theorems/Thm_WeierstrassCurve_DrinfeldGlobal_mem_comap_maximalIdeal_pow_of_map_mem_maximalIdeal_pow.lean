-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/06d051f3-e18f-549c-9ed6-0502baf29a1a
-- title:
--   Formal chart at the origin detects powers of 𝔭
-- statement:
--   Let $T$ be a commutative local ring and $W$ a Weierstrass curve over $T$. Write $A$ for the origin chart ring `OriginChartRing W`, the degree-zero homogeneous localisation away from the coordinate $Y$ of the graded quotient $T[X_0,X_1,X_2]/(F_W)$ by the Weierstrass cubic, with grading induced from the homogeneous submodules; inside $A$ one has the elements `xOverY W` $=X/Y$ and `zOverY W` $=Z/Y$, and a copy of $T$ coming from degree zero. Let $\Phi : A \to T[[X]]$ be a ring homomorphism subject to three pinning conditions: it carries each scalar $t \in T$ (via the degree-zero inclusion) to the constant series $C\,t$; it carries $X/Y$ to $-X$; and it carries $Z/Y$ to $-$`W.formalW`, the series whose $n$-th coefficient is the $n$-th coefficient of the $n$-th iterate of the substitution `W.wSubst` started at $0$. Then for every $n : \mathbb{N}$ and every $a \in A$: if $\Phi(a)$ lies in the $n$-th power of the maximal ideal of $T[[X]]$ (namely $(\mathfrak m_T, X)^n$), then $a$ lies in the $n$-th power of the contracted ideal $\Phi^{-1}(\mathfrak m_{T[[X]]})$. Note that the conclusion is the power of the contraction, which is stronger than membership in the contraction of the power.
--
--   This is the statement that the formal parametrisation of a Weierstrass curve at the origin is level-exact: it detects the filtration by powers of the prime $\mathfrak p = \Phi^{-1}(\mathfrak m_T, X)$ cutting out the origin section. It is used in the construction of the comparison map from the localisation of the origin chart ring at $\mathfrak p$ to $T[[X]]$ and the proof that this map is faithfully flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow.lean

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

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW)
    (n : ℕ) (a : OriginChartRing W) (ha : Φ a ∈ maximalIdeal (PowerSeries T) ^ n) :
    a ∈ Ideal.comap Φ (maximalIdeal (PowerSeries T)) ^ n := by sorry
