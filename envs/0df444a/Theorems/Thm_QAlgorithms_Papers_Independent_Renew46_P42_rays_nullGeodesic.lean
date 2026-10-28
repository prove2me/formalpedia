-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_rays_nullGeodesic
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.rays_nullGeodesic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:26:45.416986+00:00
-- url     : https://prove2.me/theorems/fded2d4c-b931-495a-8140-110966d41ac2
-- title:
--   Hamiltonian rays follow null Gordon geodesics
-- statement:
--   Let $c>0$ and let $n\ge1$, $|\mathbf u|<c$ be $C^2$ optical data on an open spacetime patch. Write $g$, $G$ for the constructed Gordon metrics and $H$ for (34). On an open time interval take a $C^2$ curve $q(t)=(ct,\mathbf x(t))$ in that patch and $C^1$ nonzero spatial momentum $\mathbf k(t)$ satisfying $\dot{\mathbf x}=\partial_{\mathbf k}H$ and $\dot{\mathbf k}=-\partial_{\mathbf x}H$, including the possible time dependence of the optical data. Then
--
--   $$g_q(\dot q,\dot q)=0,\qquad \ddot q^\mu+\Gamma^\mu_{\alpha\beta}(q)\dot q^\alpha\dot q^\beta=a(t)\dot q^\mu$$
--
--   for some scalar at each time, where $\Gamma$ is computed from $g$ and $G$. At every event, for any rest-frame displacement $v$, its Lorentz boost $\Lambda v$ satisfies
--
--   $$g(\Lambda v,\Lambda v)=(v^0)^2/n^2-\sum_{i=1}^3(v^i)^2.$$
--
--   This is the local unparameterized null-geodesic statement attributed to Gordon; it asserts no global Lorentzian minimizing property.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 6, §III D, (50)–(51): null geodesics of Gordon metric

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.6, (50)–(51), Gordon [2]: rays of the laboratory Hamiltonian are null
geodesics in laboratory time, with acceleration parallel to their tangent.
This avoids any global minimum claim for Lorentzian length. -/
theorem rays_nullGeodesic (c : ℝ) (P : OpticalPatch c)
    (I : Set ℝ) (q : ℝ → V4) (k : ℝ → V3)
    (hc : 0 < c) (hI : IsOpen I)
    (hq : ContDiffOn ℝ 2 q I) (hkreg : ContDiffOn ℝ 1 k I)
    (himage : ∀ t ∈ I, q t ∈ P.domain)
    (hkn : ∀ t ∈ I, k t ≠ 0)
    (ht : ∀ t ∈ I, q t 0 = c * t)
    (hposition : ∀ t ∈ I,
      spatial (deriv q t) = rayVelocity c (P.index (q t)) (P.flow (q t)) (k t))
    (hmomentum : ∀ t ∈ I,
      deriv k t = -spatial (gradient (fun x =>
        rayHamiltonian c (P.index x) (P.flow x) (k t)) (q t))) :
    (∀ t ∈ I, quadratic (patchDown P (q t)) (deriv q t) = 0 ∧
      ∃ a : ℝ, covAcceleration (patchDown P) (patchUp P) q t = a • deriv q t) ∧
    (∀ x ∈ P.domain, ∀ v : V4,
      quadratic (patchDown P x) (apply4 (lorentzBoost c (P.flow x)) v) =
        (v 0) ^ 2 / (P.index x) ^ 2 - ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
