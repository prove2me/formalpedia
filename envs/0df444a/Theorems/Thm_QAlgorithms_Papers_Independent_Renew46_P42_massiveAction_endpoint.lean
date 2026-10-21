-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_massiveAction_endpoint
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.massiveAction_endpoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:25:42.420063+00:00
-- url     : https://prove2.me/theorems/58002cf8-c336-4fdb-a298-a8468a37dada
-- title:
--   Degenerate optical Legendre transform and massive endpoint action
-- statement:
--   Let $c,m>0$ and let $g$, $G=g^{-1}$ be the Gordon metrics of $C^2$ optical data $n\ge1$, $|\mathbf u|<c$ on an open spacetime patch $D$. Consider a $C^2$ family $q(s,z)$, defined near $[0,1]\times E$ for an open endpoint set $E\subset D$, of affinely parametrized future timelike $g$-geodesics with fixed initial endpoint $q(0,z)=z_0$, final endpoint $q(1,z)=z$ for $z\in E$, and images in $D$. Require $g(\dot q,\dot q)>0$ and $\dot q^0>0$. Define
--
--   $$S(z)=-mc\int_0^1\sqrt{g_{q(s,z)}(\dot q,\dot q)}\,ds.$$
--
--   The endpoint function is differentiable and, with $v=\partial_sq(1,z)$,
--
--   $$-\partial_\mu S(z)=\frac{mc\,g_{\mu\nu}(z)v^\nu}{\sqrt{g_z(v,v)}},\qquad G^{\mu\nu}\partial_\mu S\partial_\nu S=m^2c^2.$$
--
--   For the massless Hamiltonian (34), $\mathbf k\cdot\partial_{\mathbf k}H-H=0$ for every nonzero $\mathbf k$. For a timelike laboratory tangent $(c,\mathbf v)$, the massive laboratory-time Lagrangian is
--
--   $$L=-mc\sqrt{c^2-|\mathbf v|^2+(n^{-2}-1)\gamma^2(c-\mathbf u\cdot\mathbf v/c)^2}=-mc\sqrt{g((c,\mathbf v),(c,\mathbf v))}.$$
--
--   This constructs the principal function on extremals; the auxiliary mass is a regularization and does not assign a photon rest mass.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 5, §III C, (39)–(49): degenerate optical Legendre transform and massive action

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.5–6, (39)–(49): zero massless Legendre transform and the massive
proper-length action on an actual local geodesic endpoint congruence.
The mass m is an artificial regularization, not a photon mass. -/
theorem massiveAction_endpoint (c m : ℝ) (P : OpticalPatch c)
    (q : ℝ → V4 → V4) (z zBase : V4) (J : Set ℝ) (E : Set V4)
    (hc : 0 < c) (hm : 0 < m) (hz : z ∈ E)
    (hE : IsOpen E) (hEP : E ⊆ P.domain)
    (hJ : IsOpen J) (h01 : Icc (0 : ℝ) 1 ⊆ J)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E))
    (hend : ∀ y ∈ E, q 0 y = zBase ∧ q 1 y = y)
    (himage : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1, q s y ∈ P.domain)
    (htime : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < deriv (fun t => q t y) s 0)
    (htimelike : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s))
    (hgeo : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      covAcceleration (patchDown P) (patchUp P) (fun t => q t y) s = 0) :
    (∀ k : V3, k ≠ 0 →
      dot3 k (rayVelocity c (P.index z) (P.flow z) k) -
        rayHamiltonian c (P.index z) (P.flow z) k = 0) ∧
    (∀ v : V3, 0 < quadratic (patchDown P z) ![c, v 0, v 1, v 2] →
      massiveLagrangian c (P.index z) m (P.flow z) v =
        -m * c * Real.sqrt (quadratic (patchDown P z) ![c, v 0, v 1, v 2])) ∧
    DifferentiableAt ℝ (endpointAction P m q) z ∧
    (∀ i : Fin 4, -cartesianPartial (endpointAction P m q) z i =
      massiveCovector c m (patchDown P z) (deriv (fun s => q s z) 1) i) ∧
    quadratic (patchUp P z) (gradient (endpointAction P m q) z) = m ^ 2 * c ^ 2 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
