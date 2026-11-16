-- Prove2me | Theorems.Thm_PrivateRoutingSignaling_PTAS_Supplement_smoothing_bounds
-- name    : PrivateRoutingSignaling.PTAS.Supplement.smoothing_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:50:48.886035+00:00
-- url     : https://prove2.me/theorems/8cf60415-5d98-4c1a-ad2c-7eeb0023eb6f
-- title:
--   Remark 6.6 — continuous three-piece smoothing keeps all four dual bounds, with Lipschitz constant at most $2N/\eta$
-- statement:
--   Let $G$ be a cubic graph on $N>0$ vertices and $0<\eta\le\frac12$. In the construction of §6, replace the jumps of $g$ and $h$ in the hard state, and of each $\ell$ in the states $P_U$, by linear pieces increasing from zero to one on
--
--   $$
--   \Bigl[\tfrac1N,\tfrac{1+\eta}N\Bigr],\qquad \Bigl[\tfrac{1-\eta}{2N},\tfrac1{2N}\Bigr],\qquad \Bigl[\tfrac{Y_{U,R_j}}2,\tfrac{(1+\eta)Y_{U,R_j}}2\Bigr],
--   $$
--
--   respectively, keeping each function constant outside its interval, and write $\tilde D^\theta$, $\tilde D^{\mathrm{aux}}$ for the resulting dual functions. Then, with $Y$ the designated dual solution and $\|\cdot\|_1$ the entrywise $\ell^1$ distance,
--
--   1. $\tilde D^H(Y)\ge-\frac{\mathrm{MaxCut}(G)}{4N}-2\eta$;
--   2. $\tilde D^H(y)\le-\frac{\mathrm{MaxCut}(G)}{4N}+\frac1N\|y-Y\|_1$ for every nonnegative dual matrix $y$;
--   3. $\tilde D^{\mathrm{aux}}(Y)\ge\frac{1-\eta}8$;
--   4. $\tilde D^{\mathrm{aux}}(y)\le\frac{1+\eta}8-\frac{1-\eta}{32N}\|y-Y\|_1$ for every nonnegative dual matrix $y$;
--   5. every latency function of the smoothed instance is continuous on $[0,1]$, has at most three linear pieces there, and is Lipschitz on $[0,1]$ with constant at most $\frac{2N}\eta$.
--
--   These bounds transfer the analysis of the discontinuous construction to continuous latency functions, at the price of an error linear in $\eta$, and they feed Lemma 6.7.
--
--   **Formalization Note** $\mathrm{MaxCut}(G)$ is the published `MISInducedMinor.maxCut`, the largest number of edges crossing a vertex bipartition. $\tilde D^\theta$ is the infimum over all real flows. The Lipschitz bound is stated as $|c(x)-c(x')|\le\frac{2N}\eta|x-x'|$ for $x,x'\in[0,1]$.
--
--   Differences from the source:
--   - encoding: "the resulting dual functions" and bounds for y → dual functions of the explicit smoothed latencies, with the two upper bounds for every nonnegative dual matrix y; reason: y ranges over the dual feasible region y ≥ 0 as in Lemmas 6.2 and 6.5 (pp. 33, 36)
--   - encoding: "at most three linear pieces and Lipschitz constant at most 2N/η" → on the relevant range [0, 1]: breakpoints 0 ≤ t_1 ≤ t_2 ≤ 1 with an affine function on each of the three intervals, and |c(x) − c(x′)| ≤ (2N/η)|x − x′|; reason: latencies are only evaluated at loads in [0, 1] (§2.1, p. 5)
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), Remark 6.6, pp. 36–37 (PDF pp. 36–37); construction §§6.1–6.3 pp. 31–36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_MISInducedMinor_maxCut
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_ShortPathInstance

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- Remark 6.6 (Cheng–Jiang, STOC 2027 submission #439, pp. 36–37). For a cubic graph on
`N > 0` vertices and `0 < η ≤ 1/2`, the smoothed dual functions satisfy the four displayed
bounds, and every smoothed latency is continuous on `[0,1]`, has at most three linear pieces and
Lipschitz constant at most `2N/η` there. -/
theorem smoothing_bounds (N : ℕ) (hN : 0 < N) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 3) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    -((MISInducedMinor.maxCut G : ℕ) : ℝ) / (4 * N) - 2 * η ≤
        ShortPath.dTilde N G η (ShortPath.hState N) (ShortPath.Y N G) ∧
      (∀ y : DualMatrix (ShortPath.network N), DualNonneg y →
        ShortPath.dTilde N G η (ShortPath.hState N) y ≤
          -((MISInducedMinor.maxCut G : ℕ) : ℝ) / (4 * N) + l1Dist y (ShortPath.Y N G) / N) ∧
      (1 - η) / 8 ≤ ShortPath.dauxTilde N G η (ShortPath.Y N G) ∧
      (∀ y : DualMatrix (ShortPath.network N), DualNonneg y →
        ShortPath.dauxTilde N G η y ≤
          (1 + η) / 8 - (1 - η) / (32 * N) * l1Dist y (ShortPath.Y N G)) ∧
      ∀ θ a, ContinuousOn (ShortPath.latency N G η θ a) (Set.Icc 0 1) ∧
        AtMostThreePieces (ShortPath.latency N G η θ a) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
          |ShortPath.latency N G η θ a x - ShortPath.latency N G η θ a x'| ≤
            2 * N / η * |x - x'| := by sorry

end PrivateRoutingSignaling.PTAS.Supplement
