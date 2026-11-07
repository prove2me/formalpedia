-- Prove2me | Theorems.Thm_PolySphereLP_eq_35_spherical_hypercontractivity
-- name    : PolySphereLP.eq_35_spherical_hypercontractivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:37.576098+00:00
-- url     : https://prove2.me/theorems/56fa587c-d93b-4e0c-8e4f-3cf6df44aab4
-- title:
--   Eq. (35) — hypercontractivity on the sphere
-- statement:
--   Let $m\ge0$, $k\ge0$ and $p\ge2$ real, and let $\sigma_m$ be the uniform probability measure on $S^{m-1}$. For every homogeneous polynomial $G$ on $\mathbb R^m$ of degree at most $k$,
--   $$\|G\|_{L^p(\sigma_m)}\le(p-1)^{k/2}\,\|G\|_{L^2(\sigma_m)}. \tag{35}$$
--
--   It is the transfer of Gaussian hypercontractivity (34) to the sphere, and is used on the solution sphere (Lemma 2.6) and on the coefficient sphere (Lemma 3.1).
--
--   **Formalization Note** "Of degree at most $k$" is the hypothesis of (34), which (35) transfers: $G$ is homogeneous of some degree $j\le k$. Norms are taken in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: "For homogeneous G" under the hypotheses (p ≥ 2, deg G ≤ k) of (34) → G homogeneous of degree j for some j ≤ k, p ≥ 2 real; reason: (35) is stated as the transfer of (34), whose hypotheses it keeps
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.5, p.14, eq. (35)

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Eq. (35) (Hypercontractivity on the sphere).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §2.5, p.14, eq. (35).

For homogeneous `G` (of degree `≤ k`) on `ℝ^m` and `p ≥ 2`, with `σ_m` the uniform probability
measure on `S^{m−1}`: `‖G‖_{L^p(σ_m)} ≤ (p − 1)^{k/2} ‖G‖_{L²(σ_m)}`.

**Formalization Note.** The hypotheses `p ≥ 2, deg G ≤ k` are those of (34), which (35) transfers;
`G` is homogeneous of some degree `j ≤ k`. Norms are `eLpNorm` in `[0,∞]`; `(p−1)^{k/2}` is a real
power. `m` is arbitrary. -/
theorem eq_35_spherical_hypercontractivity (m k j : ℕ) (hjk : j ≤ k)
    (G : MvPolynomial (Fin m) ℝ) (hG : G.IsHomogeneous j) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x => eval x G) (ENNReal.ofReal p) (SphereSOS.Rate.sigma m) ≤
      ENNReal.ofReal ((p - 1) ^ ((k : ℝ) / 2)) *
        eLpNorm (fun x => eval x G) 2 (SphereSOS.Rate.sigma m) := by sorry

end PolySphereLP
