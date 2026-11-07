-- Prove2me | Theorems.Thm_PolySphereLP_lemma_2_6_nonnegative_test
-- name    : PolySphereLP.lemma_2_6_nonnegative_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:55.214559+00:00
-- url     : https://prove2.me/theorems/c9258646-0086-413e-a856-36dd5d20b600
-- title:
--   Lemma 2.6 — an elementary nonnegative-test estimate
-- statement:
--   Let $n\ge3$ and let $q$ be even. If $g\in\mathbb R[x]_{\le q}$ is nonnegative on the sphere and $\mu_g=\int g\,d\sigma$, then
--   $$\|\Pi_qg\|_{L^2(\sigma)}\le3^q\,\mu_g. \tag{36}$$
--
--   The estimate controls the covariance of a test against the calibration direction in the main lemma.
--
--   **Formalization Note** $g$ need not be homogeneous, and $\Pi_q$ is the $L^2(\sigma)$ projection onto $\mathcal H_{n,q}$.
--
--   Differences from the source:
--   - generalization: standing assumptions d ≥ 2 even, q ≥ 2d, 2d ∣ q (§2, p.9) → q even; reason: the proof uses only that q is even (symmetrization and homogenization to degree q); the standing case is included
--   - encoding: ‖Π_q g‖_{L²(σ)} → √(∫ (Π_q g)² dσ); reason: definition of the L² norm
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma 2.6, p.15, eq. (36)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_piProj
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma 2.6 (An elementary nonnegative-test estimate).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma 2.6, p.15, eq. (36).

If `g ∈ ℝ[x]_{≤q}` is nonnegative on the sphere and `μ_g = ∫ g dσ`, then
`‖Π_q g‖_{L²(σ)} ≤ 3^q μ_g`.

**Formalization Note.** Standing assumptions (p.9): `n ≥ 3`; of `q ≥ 2d, 2d ∣ q` only the evenness
of `q` is kept (the proof symmetrizes `g` and homogenizes its even components to degree `q`). `g` is
not homogeneous; `Π_q` is the `L²(σ)` projection `piProj`. -/
theorem lemma_2_6_nonnegative_test (n q : ℕ) (hn : 3 ≤ n) (hq : Even q)
    (g : MvPolynomial (Fin n) ℝ) (hgdeg : g.totalDegree ≤ q)
    (hg : ∀ x ∈ SphereSOS.Rate.sphere n, 0 ≤ eval x g) :
    Real.sqrt (∫ x, eval x (piProj n q g) ^ 2 ∂(SphereSOS.Rate.sigma n)) ≤
      3 ^ q * ∫ x, eval x g ∂(SphereSOS.Rate.sigma n) := by sorry

end PolySphereLP
