-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem62
-- name    : ShockWear.Inherit.Supplement.theorem62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:02:10.047799+00:00
-- url     : https://prove2.me/theorems/1468f396-cc78-4e0b-ab1d-ff77e854414d
-- title:
--   Theorem 6.2 — a random threshold gives a logarithmically convex density
-- statement:
--   Shocks arrive at rate $\lambda>0$ with independent magnitudes of common distribution $F$, and the device fails at the first shock whose magnitude exceeds a threshold that is itself random, with distribution $G$ and independent of the magnitudes. Both $F$ and $G$ are distributions on $[0,\infty)$. The probability of surviving $k$ shocks is (6.3)
--   $$\bar P_k=\int_0^\infty[F(x)]^k\,dG(x),\qquad k=0,1,\dots.$$
--   Then the survival function $\bar H$ of (2.1) has a density that is logarithmically convex on $(0,\infty)$: the density $h$ of (2.3) satisfies, for every $x>0$ and $0<s\leq t$,
--   $$h(x+s)\,h(t)\leq h(x+t)\,h(s).$$
--
--   Thus a random threshold always produces a decreasing-hazard (indeed log-convex density) life distribution, whatever the shock law.
--
--   **Formalization Note** $F$ and $G$ are probability measures $\mu,\nu$ on $\mathbb R$ with no mass on $(-\infty,0)$, $F(x)=\mu(-\infty,x]$, and the integral (6.3) is taken against $\nu$ over $\mathbb R$ (the same as over $[0,\infty)$; the integrand is bounded and monotone, so integrable). The density is the explicit series (2.3) built from these $\bar P_k$. Log-convexity is the cross-multiplied statement that $h(x+t)/h(t)$ is increasing in $t>0$; it agrees with convexity of $\log h$ when $h>0$, and holds trivially in the degenerate case $h\equiv0$ (threshold above every magnitude almost surely).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 647, Theorem 6.2, display (6.3); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

open MeasureTheory

/-- Theorem 6.2: with a random threshold, `P̄_k = ∫₀^∞ [F(x)]^k dG(x)` as in (6.3),
the density (2.3) of `H̄` is logarithmically convex on `(0, ∞)`. -/
theorem theorem62 (lam : ℝ) (hlam : 0 < lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0) :
    IsLogConvexDens
      (shockDens lam (fun k => ∫ x, ((μ (Set.Iic x)).toReal) ^ k ∂ν)) := by sorry

end ShockWear.Inherit.Supplement
