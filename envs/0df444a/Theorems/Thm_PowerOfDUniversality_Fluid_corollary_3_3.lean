-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_corollary_3_3
-- name    : PowerOfDUniversality.Fluid.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:06.610916+00:00
-- url     : https://prove2.me/theorems/f22bb98c-a7da-47ce-b001-a7a80d0d9707
-- title:
--   Corollary 3.3 — under the S-coupling, Q_m^{CJSQ} is sandwiched between JSQ and MJSQ tail sums, almost surely for all t
-- statement:
--   Fix $N\ge 1$ servers, a buffer $b\ge 1$, an arrival rate $\lambda\ge 0$, an integer $n$ with $n+1\le N$ and a scheme $\Pi$ of the class CJSQ($n$). Three S-coupled systems (driven by the same arrival clock and the same departure clocks of the $k$-th ordered server) run JSQ, $\Pi$ and MJSQ($n$), from initial states ordered at every level:
--   $$\sum_{i\ge m}Q^{JSQ}_i(0)\le\sum_{i\ge m}Q^{CJSQ}_i(0)\le\sum_{i\ge m}Q^{MJSQ}_i(0)\qquad(m\ge 1).$$
--   Then almost surely, for all $t\ge 0$ and every $m\ge 1$,
--   1. $$Q^{CJSQ}_m(t)\ge\sum_{i=m}^{b}Q^{JSQ}_i(t)-\sum_{i=m+1}^{b}Q^{MJSQ}_i(t)+L^{JSQ}(t)-L^{MJSQ}(t),$$
--   2. $$Q^{CJSQ}_m(t)\le\sum_{i=m}^{b}Q^{MJSQ}_i(t)-\sum_{i=m+1}^{b}Q^{JSQ}_i(t)+L^{MJSQ}(t)-L^{JSQ}(t).$$
--
--   These two-sided bounds transfer fluid and diffusion limits of JSQ and MJSQ($n$) to every scheme of the class CJSQ($n$).
--
--   **Formalization Note** "Provided the inequalities hold at time $t=0$" is read as the initial ordering hypothesis of Proposition 3.2, which is how the corollary is used on p. 27. The initial states may be random (they are coupled through the same sample point). The bounds are stated in the integers; for $m>b$ the sums are empty.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 13, Corollary 3.3

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Corollary 3.3** (p. 13, pathwise sandwich under the S-coupling). Three S-coupled systems
(`N ≥ 1` servers, buffer `b ≥ 1`, rate `λ ≥ 0`, the same clock and marks) run JSQ, a scheme
`Π ∈` CJSQ(n) and MJSQ(n) (`n + 1 ≤ N`), from initial occupancy vectors ordered as in
Proposition 3.2 at `t = 0` for every level. Then almost surely, for all `t ≥ 0` and every
`m ≥ 1`:

1. `Q^{CJSQ}_m(t) ≥ ∑_{i=m}^{b} Q^{JSQ}_i(t) − ∑_{i=m+1}^{b} Q^{MJSQ}_i(t) + L^{JSQ}(t) − L^{MJSQ}(t)`;
2. `Q^{CJSQ}_m(t) ≤ ∑_{i=m}^{b} Q^{MJSQ}_i(t) − ∑_{i=m+1}^{b} Q^{JSQ}_i(t) + L^{MJSQ}(t) − L^{JSQ}(t)`. -/
theorem corollary_3_3 (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (n : ℕ) (hn : n + 1 ≤ N) (pol : Scheme) (hpol : IsCJSQ n pol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sysJ sysC sysM : System P N b lam) (hJC : sysJ.ξ = sysC.ξ) (hJM : sysJ.ξ = sysM.ξ)
    (h0JC : ∀ ω (m : ℕ), 1 ≤ m → tailSum (sysJ.Q0 ω) m ≤ tailSum (sysC.Q0 ω) m)
    (h0CM : ∀ ω (m : ℕ), 1 ≤ m → tailSum (sysC.Q0 ω) m ≤ tailSum (sysM.Q0 ω) m) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ m : ℕ, 1 ≤ m →
      ((tailSum (sysJ.occ jsq ω t) m : ℤ) - tailSum (sysM.occ (mjsq n) ω t) (m + 1)
          + sysJ.overflow jsq ω t - sysM.overflow (mjsq n) ω t
        ≤ (sysC.occ pol ω t m : ℤ)) ∧
      ((sysC.occ pol ω t m : ℤ)
        ≤ (tailSum (sysM.occ (mjsq n) ω t) m : ℤ) - tailSum (sysJ.occ jsq ω t) (m + 1)
          + sysM.overflow (mjsq n) ω t - sysJ.overflow jsq ω t) := by sorry

end PowerOfDUniversality.Fluid
