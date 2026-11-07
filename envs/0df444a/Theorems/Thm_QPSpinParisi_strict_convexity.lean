-- Prove2me | Theorems.Thm_QPSpinParisi_strict_convexity
-- name    : QPSpinParisi.strict_convexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:55.625981+00:00
-- url     : https://prove2.me/theorems/36a2779f-7a13-423e-a5d0-18e6e83aef31
-- title:
--   pp.23–25 — $\gamma\mapsto P_\xi(\gamma)$ is strictly convex on $\mathcal U$
-- statement:
--   The Parisi functional $P_\xi$ is strictly convex on the convex set $\mathcal U$: for distinct $\gamma_0,\gamma_1\in\mathcal U$ and $\lambda\in(0,1)$,
--   $$P_\xi((1-\lambda)\gamma_0+\lambda\gamma_1)<(1-\lambda)P_\xi(\gamma_0)+\lambda P_\xi(\gamma_1).$$
--   This yields uniqueness of the minimizer in Theorem 1.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - encoding: functions on $[0,1)$ → `Ico 0 1 → ℝ`, extended by $0$ under integrals; reason: integrals over $[0,1]$ do not see the point $1$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), pp.23–25 (PDF pp.23–25)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_USet
import Definitions.Def_QPSpinParisi_Pf

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), pp.23–25, PDF pp.23–25: "We will show the functional `γ ↦ P_ξ(γ)` is strictly convex on `U`." -/
theorem strict_convexity (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) :
    StrictConvexOn ℝ USet (Pf W) := by sorry

end QPSpinParisi
