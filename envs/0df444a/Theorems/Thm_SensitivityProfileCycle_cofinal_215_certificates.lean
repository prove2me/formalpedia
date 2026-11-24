-- Prove2me | Theorems.Thm_SensitivityProfileCycle_cofinal_215_certificates
-- name    : SensitivityProfileCycle.cofinal_215_certificates
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-24T08:27:11.694807+00:00
-- url     : https://prove2.me/theorems/4d1841a1-42e4-425c-be39-0fbb8a5cd5af
-- title:
--   Finite profile cycles approaching the 2.15 sensitivity exponent from below
-- statement:
--   For every integer $k\ge 0$, find a finite recursive-profile cycle with vertex count $K$, period $L$, and return factor $R>1$ satisfying
--   $$
--   R^{43k+42}\le (K^L)^{20(k+1)}.
--   $$
--
--   The cycle must satisfy the graph, labeling, recipe, and profile inequalities in `SensitivityProfileCycle.Certificate`. Its data may depend on $k$. Since $R>1$, the integer test asks that the cycle's score satisfy
--   $$
--   \frac{\log(K^L)}{\log R}\ge \frac{43}{20}-\frac{1}{20(k+1)}.
--   $$
--
--   This is an open sufficient condition for the 2.15 mission. It allows a sequence of finite scores converging to 2.15 from below. A single cycle at or above 2.15 would satisfy every test.
-- source:
--   Open approximation problem derived here from the profile-cycle certificate in https://prove2.me/theorems/6c031b2d-eb14-46d2-8d9e-f2db70527660 and its proved finite-seed bounds in https://prove2.me/theorems/dd31034a-13ba-4d9d-8e2f-0087ac70bad8. The exponents 43k+42 and 20(k+1) give the exact subcritical target 43/20 - 1/(20(k+1)). The source of the campaign objective is https://github.com/bigospeedrun/site/issues/2.

import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.cofinal_215_certificates (k : ℕ) :
    ∃ c : SensitivityProfileCycle.Certificate,
      1 < c.radius ∧
      c.radius ^ (43 * k + 42) ≤ (c.vertices ^ c.period) ^ (20 * (k + 1)) := by sorry
