-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_R_properties
-- name    : VerticalOwnership.CheapTalk.R_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:28.464514+00:00
-- url     : https://prove2.me/theorems/78f1c1f5-2a1b-4541-b7bf-31a6a7cee6c8
-- title:
--   Proof of Theorem 2, p. 46 — R is increasing on (0, ∞), R(0+) = z_s, R(∞) = 1, and z_s < R < 1
-- statement:
--   In the model of the mission, consider for $d>0$
--   $$R(d)=\frac1d\int_{F^{-1}(z_s)}^{d+F^{-1}(z_s)}F(x)\,dx .$$
--   Then:
--   1. $R$ is strictly increasing on $(0,\infty)$;
--   2. $R(d)\to z_s$ as $d\to0^+$;
--   3. $R(d)\to1$ as $d\to\infty$;
--   4. $z_s<R(d)<1$ for every $d>0$.
--
--   These properties give the range of the threshold $\underline{\underline{\beta}}$ and make the inverse $R^{-1}$ used in Theorem 2(ii) well defined on $(z_s,1)$.
--
--   **Formalization Note** The paper says "monotonically increasing"; its derivative computation gives a strictly positive derivative, and the strict version is what the inverse $R^{-1}$ requires, so strict monotonicity is stated.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 46, Appendix E, Proof of Theorem 2(i), after (E.2)

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem R_properties (M : Model) (hM : M.Standing) :
    StrictMonoOn M.R (Set.Ioi 0) ∧
    Tendsto M.R (𝓝[>] 0) (𝓝 M.zs) ∧
    Tendsto M.R atTop (𝓝 1) ∧
    ∀ d : ℝ, 0 < d → M.zs < M.R d ∧ M.R d < 1 := by sorry

end VerticalOwnership.CheapTalk
