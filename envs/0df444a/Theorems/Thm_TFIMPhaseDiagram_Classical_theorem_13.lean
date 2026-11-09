-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_theorem_13
-- name    : TFIMPhaseDiagram.Classical.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:54.311555+00:00
-- url     : https://prove2.me/theorems/e5c3723c-6d63-430a-8115-d1aae5594c51
-- title:
--   Theorem 13 — All-tilt covariance implies ATE and KL contraction
-- statement:
--   Let $\mu=\bigotimes_{i=1}^n\mu_i$, where each $\mu_i$ is an arbitrary Borel probability measure on the Euclidean unit sphere in $\mathbb R^N$, with $n,N\ge1$. Let $J\succeq0$ and $d\nu/d\mu\propto\exp(\frac12\sum_{i,j}J_{ij}\langle x_i,x_j\rangle)$. Suppose every linear tilt of every $\mu_i$ has covariance operator norm at most $\rho$, and $\|J\|_{\rm op}\rho<1$. Then
--   $$\operatorname{Ent}_\nu(f)\le C\sum_i\mathbb E\operatorname{Ent}_{\nu(\cdot\mid X_{-i})}(f),\qquad C=\frac1{1-\|J\|_{\rm op}\rho},$$
--   for every nonnegative integrable measurable $f$, and each block Glauber step contracts KL divergence by exactly the factor $1-1/(Cn)$. The contraction is stated for arbitrary initial probability laws absolutely continuous with respect to $\nu$.
--
--   The continuous-sphere domain and extended entropy values are preserved. The result turns all-tilt covariance control into the required mixing inequality.
--
--   Differences from the source:
--   - encoding: all-tilt covariance operator norm, ATE and KL contraction → Borel measures on unit-sphere subtypes, directional variances, extended nonnegative entropy and KL; reason: These are the same continuous measures and inequalities; infinite entropy and divergence are preserved.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.8 = PDF p.8, Theorem 13

import Definitions.Def_TFIMPhaseDiagram_Classical_entropy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Theorem 13, p.8: continuous sphere laws, ATE, and the exact KL contraction factor. -/
theorem theorem_13 (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (μ : Fin n → Measure (Sphere N)) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosSemidef)
    (ρ : ℝ) (hsemi : ∀ i (w : EuclideanSpace ℝ (Fin N)),
      sphereCovNorm (tilt (μ i) (fun x => dot w x.val)) ≤ ρ)
    (hsub : realOpNorm J * ρ < 1) :
  let V := sphereInteraction J
  let ν := tilt (Measure.pi μ) V
  let C := 1/(1-realOpNorm J*ρ)
  ATE ν C ∧
  ∀ (ξ : Measure (Fin n → Sphere N)), IsProbabilityMeasure ξ → ξ ≪ ν →
    klDiv (glauberStep μ V ξ) ν ≤ ENNReal.ofReal (1-1/(C*n)) * klDiv ξ ν := by sorry
end TFIMPhaseDiagram.Classical
