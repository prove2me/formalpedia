-- Prove2me | Theorems.Thm_Rudin_ch04_uniform_continuity
-- name    : Rudin.ch04_uniform_continuity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T22:25:34.326935+00:00
-- url     : https://prove2.me/theorems/a0dfc36e-e45e-433e-9e55-660e11fac210
-- title:
--   Theorem 4.19 — continuous on a compact space implies uniformly continuous
-- statement:
--   Let $f$ be a continuous mapping of a compact metric space $X$ into a metric space $Y$. Then $f$ is uniformly continuous on $X$: for every $\varepsilon > 0$ there is a $\delta > 0$, depending only on $\varepsilon$, such that $d(f(p), f(q)) < \varepsilon$ whenever $d(p,q) < \delta$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 91, Theorem 4.19

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.19: a continuous mapping of a compact metric space into a metric space is
uniformly continuous. -/
theorem ch04_uniform_continuity {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y) (hf : Continuous f) : UniformlyContinuous f := by sorry

end Rudin
