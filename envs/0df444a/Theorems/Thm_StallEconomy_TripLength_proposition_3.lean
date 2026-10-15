-- Prove2me | Theorems.Thm_StallEconomy_TripLength_proposition_3
-- name    : StallEconomy.TripLength.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:24.746282+00:00
-- url     : https://prove2.me/theorems/43f1d7e0-87e1-4b14-ba4c-ba059e517b60
-- title:
--   Proposition 3, p. 18 — mean and variance of the within-radius trip length L_r, both increasing in R and decreasing in r
-- statement:
--   Fix the Euclidean edge length $R>0$ of the diamond service zone $\mathcal Z_R = \{|x|+|y|\le R/\sqrt2\}$ and a walking radius $r$ with $0\le r\le R/\sqrt2$. The stall $A$ is uniform on the inner diamond $\mathcal I_{R,r} = \{|x|+|y|\le R/\sqrt2-r\}$, the next customer $B$ is uniform on $\mathcal Z_R$, independently, and the stall's repositioning trip length is $L_r = \max\{|A-B|-r,0\}$ with $|\cdot|$ the Manhattan distance. Then:
--
--   1. $$\mathbb E[L_r] = \frac{7\sqrt2\,R^3-22R^2r+2\sqrt2\,Rr^2+12r^3}{15R^2};$$
--   2. $$\operatorname{Var}(L_r) = \frac{22R^6-22\sqrt2\,R^5r-140\sqrt2\,R^3r^3+400R^2r^4-48\sqrt2\,Rr^5-144r^6}{225R^4};$$
--   3. $\mathbb E[L_r]$ and $\operatorname{Var}(L_r)$ are both increasing in $R$ and decreasing in $r$: for each $R>0$ they are non-increasing functions of $r$ on $[0,R/\sqrt2]$, and for each $r\ge0$ they are non-decreasing functions of $R$ on $\{R>0 : r\le R/\sqrt2\}$.
--
--   The proposition solves the paper's rendezvous problem: once the rendezvous are known to be uniform on the inner diamond, the first two moments of the trip length are explicit, and part 3 says that a longer customer walk shortens the stall's repositioning and a larger zone lengthens it.
--
--   **Formalization Note.** Parts 1 and 2 are stated for all $R>0$ and $0\le r\le R/\sqrt2$, the paper's range. Part 3 is stated about the defined quantities `meanL` and `varL` (the integrals), not about the closed forms, and "increasing/decreasing" is read as weak monotonicity on the paper's range, which is what the derivative signs on p. 51 give. $R$ is the edge length itself; the paper writes $R = 1/\sqrt\rho$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 18, Proposition 3 (I)–(III) (proof pp. 49–51)

import Mathlib
import Definitions.Def_StallEconomy_TripLength_Setting

namespace StallEconomy.TripLength

theorem proposition_3 :
    (∀ R r : ℝ, 0 < R → 0 ≤ r → r ≤ R / Real.sqrt 2 →
      meanL R r = (7 * Real.sqrt 2 * R ^ 3 - 22 * R ^ 2 * r + 2 * Real.sqrt 2 * R * r ^ 2 + 12 * r ^ 3)
        / (15 * R ^ 2)) ∧
    (∀ R r : ℝ, 0 < R → 0 ≤ r → r ≤ R / Real.sqrt 2 →
      varL R r = (22 * R ^ 6 - 22 * Real.sqrt 2 * R ^ 5 * r - 140 * Real.sqrt 2 * R ^ 3 * r ^ 3
        + 400 * R ^ 2 * r ^ 4 - 48 * Real.sqrt 2 * R * r ^ 5 - 144 * r ^ 6) / (225 * R ^ 4)) ∧
    (∀ R : ℝ, 0 < R → AntitoneOn (fun r => meanL R r) (Set.Icc 0 (R / Real.sqrt 2))) ∧
    (∀ R : ℝ, 0 < R → AntitoneOn (fun r => varL R r) (Set.Icc 0 (R / Real.sqrt 2))) ∧
    (∀ r : ℝ, 0 ≤ r → MonotoneOn (fun R => meanL R r) {R : ℝ | 0 < R ∧ r ≤ R / Real.sqrt 2}) ∧
    (∀ r : ℝ, 0 ≤ r → MonotoneOn (fun R => varL R r) {R : ℝ | 0 < R ∧ r ≤ R / Real.sqrt 2}) := by sorry

end StallEconomy.TripLength
