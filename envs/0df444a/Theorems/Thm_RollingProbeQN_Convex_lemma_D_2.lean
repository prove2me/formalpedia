-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_2
-- name    : RollingProbeQN.Convex.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:33.091069+00:00
-- url     : https://prove2.me/theorems/361ed56e-dff8-48f3-b928-99873a43bb7d
-- title:
--   Lemma D.2 — growth of the mass: $\sqrt{A_N}\ge\frac12\sum_{k<N}\sqrt{\lambda_k}$
-- statement:
--   Under the assumptions of Lemma D.1 (an A-HPE run up to horizon $N$ for a convex differentiable $F$ with a minimizer, $\sigma\in(0,1)$),
--
--   $$\sqrt{A_N}\ \ge\ \frac12\sum_{k=0}^{N-1}\sqrt{\lambda_k},\qquad\text{hence}\qquad A_N\ \ge\ \frac14\Big(\sum_{k=0}^{N-1}\sqrt{\lambda_k}\Big)^2 .$$
--
--   Large stepsizes make the mass grow; with $\lambda_k\ge\sigma/L_1$ this gives the smoothness branch $A_N\ge\sigma N^2/(4L_1)$ of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: the recursion runs for k = 0, 1, … and the claim is for every k ≥ 0 → an A-HPE run up to an arbitrary horizon N, the claim for k < N (resp. k ≤ N); reason: N is arbitrary, so every finite stretch of an infinite run is covered; same instances
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.2, p. 38

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_IsAHPERun

namespace RollingProbeQN.Convex

/-- **Lemma D.2 (Growth of `A_N`).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.2, p. 38: "`√A_N ≥ ½ ∑_{k=0}^{N−1} √λ_k`, hence `A_N ≥ ¼ (∑_{k=0}^{N−1} √λ_k)²`."

**Formalization Note.** Stated for an A-HPE run up to horizon `N` under the standing assumptions of
Appendix D.1. -/
theorem lemma_D_2 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ} {σ R : ℝ} {N : ℕ} {lam : ℕ → ℝ}
    {x y z : ℕ → EuclideanSpace ℝ (Fin d)} {A : ℕ → ℝ} {xstar : EuclideanSpace ℝ (Fin d)}
    (hconv : ConvexOn ℝ Set.univ F) (hdiff : Differentiable ℝ F)
    (hmin : IsMinOn F Set.univ xstar) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hR : ‖x 0 - xstar‖ ≤ R)
    (hrun : IsAHPERun F σ N lam x y z A) :
    1 / 2 * ∑ k ∈ Finset.range N, Real.sqrt (lam k) ≤ Real.sqrt (A N) ∧
      1 / 4 * (∑ k ∈ Finset.range N, Real.sqrt (lam k)) ^ 2 ≤ A N := by sorry

end RollingProbeQN.Convex
