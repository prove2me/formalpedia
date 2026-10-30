-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_eq_42_util_formula
-- name    : RideHailingAV.PureHV.eq_42_util_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:00.500057+00:00
-- url     : https://prove2.me/theorems/3590628e-74c2-4033-a5cf-e8d839e3271f
-- title:
--   Eqs. (42), (45) — the utilization function $\bar u$
-- statement:
--   Let $t_1(s)=as^{-r}$ with $a>0$, $0\le r<1$, and trip time $t_2>0$. Then:
--
--   1. for every $d>0$,
--   $$\bar u(d)=\frac{d\,t_2}{\tilde a d^{1/(r+1)}+t_2d}=\frac{t_2}{\tilde a d^{-r/(r+1)}+t_2};\qquad(42)$$
--   2. if $r>0$, $\bar u$ is strictly increasing on $(0,\infty)$;
--   3. if $r=0$, $\bar u(d)=t_2/(\tilde a+t_2)$ for every $d>0$.
--
--   Combined with the monotonicity of the equilibrium demand, this gives Item 3 of Proposition 1 and eq. (45).
--
--   Differences from the source:
--   - encoding: ū(d_HV) for demand rates d_HV → the identities and monotonicity for d > 0; reason: the second form of (42) divides by d and d^(−r/(r+1)) is undefined at d = 0 for r > 0; ū(0) = 0
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Appendix B.1.4, eq. (42), p. 44; eq. (45), p. 45

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_aTilde
import Definitions.Def_RideHailingAV_PureHV_util

namespace RideHailingAV.PureHV

/-- **Eqs. (42), (45) — the utilization function.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Appendix B.1.4, eq. (42), p. 44:
"`ū(d_HV) = d_HV t₂ / (ã d_HV^(1/(r+1)) + t₂ d_HV) = t₂ / (ã d_HV^(−r/(r+1)) + t₂)` (42). When
`r > 0`, the denominator, `(ã d_HV^(−r/(r+1)) + t₂)`, is strictly decreasing in `d_HV`. Thus,
`ū(d_HV)` is strictly increasing in `d_HV`." and p. 44: "When `r = 0`, the denominator in
Eq. (42), `(ã d_HV^(−r/(r+1)) + t₂)`, is a constant and equal to `(ã + t₂)`."

For `a > 0`, `0 ≤ r < 1`, `t₂ > 0`:
1. for every `d > 0`, `ū(d) = d t₂ / (ã d^(1/(r+1)) + t₂ d) = t₂ / (ã d^(−r/(r+1)) + t₂)`;
2. if `r > 0`, `ū` is strictly increasing on `(0, ∞)`;
3. if `r = 0`, `ū(d) = t₂ / (ã + t₂)` for every `d > 0` (eq. (45), p. 45). -/
theorem eq_42_util_formula (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r) (hr1 : M.r < 1)
    (ht2 : 0 < M.t2) :
    (∀ d : ℝ, 0 < d →
        util M d = d * M.t2 / (aTilde M * d ^ (1 / (M.r + 1)) + M.t2 * d) ∧
        util M d = M.t2 / (aTilde M * d ^ (-M.r / (M.r + 1)) + M.t2)) ∧
      (0 < M.r → StrictMonoOn (util M) (Set.Ioi 0)) ∧
      (M.r = 0 → ∀ d : ℝ, 0 < d → util M d = M.t2 / (aTilde M + M.t2)) := by sorry

end RideHailingAV.PureHV
