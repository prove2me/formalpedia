-- Prove2me | Theorems.Thm_ReputationLies_Matching_mps_step
-- name    : ReputationLies.Matching.mps_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:12.698651+00:00
-- url     : https://prove2.me/theorems/21398e5b-cd47-4414-8d06-896445835aa2
-- title:
--   Proof of Proposition 3, p. 40 (PDF 42) — a mean-preserving spread raises E[F(s_m)] for strictly convex F, lowers it for strictly concave F
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   For $s \in (s_L, 1]$ consider the fair gamble on the beliefs $\{s_L, s\}$ with mean $\hat s$: belief $s$ with probability $q(s) = (\hat s - s_L)/(s - s_L)$ and belief $s_L$ otherwise. Its hiring probability is
--   $$H(s) = q(s)\,F(s) + (1 - q(s))\,F(s_L).$$
--   If $F$ is strictly convex on $[0,1]$, then $H$ is strictly increasing on $(s_L, 1]$; if $F$ is strictly concave on $[0,1]$, then $H$ is strictly decreasing on $(s_L, 1]$.
--
--   A higher equilibrium threshold $b^*$ raises $s_R(b^*)$ while $s_{NR} = s_L$ stays fixed, which is a mean-preserving spread of the gamble; this step converts Proposition 2 into Proposition 3.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 40 (PDF 42), proof of Proposition 3

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proof of Proposition 3, p. 40: for the fair gamble on `{sL, s}` with mean `ŝ`, the hiring
probability is strictly increasing in `s ∈ (sL, 1]` (a mean-preserving spread) if `F` is
strictly convex on `[0, 1]`, and strictly decreasing if `F` is strictly concave. -/
theorem mps_step (P : Primitives) (hP : P.Standing) :
    (StrictConvexOn ℝ (Icc 0 1) P.F → StrictMonoOn P.gambleHire (Ioc P.sL 1)) ∧
    (StrictConcaveOn ℝ (Icc 0 1) P.F → StrictAntiOn P.gambleHire (Ioc P.sL 1)) := by sorry

end ReputationLies.Matching
