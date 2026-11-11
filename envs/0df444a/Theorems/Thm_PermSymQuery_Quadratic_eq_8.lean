-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_eq_8
-- name    : PermSymQuery.Quadratic.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:12.593819+00:00
-- url     : https://prove2.me/theorems/6e9ce800-7ea7-4873-bb58-a39d69b86fdc
-- title:
--   §3.4, Eq. (8) — quadratic sample parameters
-- statement:
--   Fix $K=10^8$. For all natural numbers $q\ge1$ and $N>Kq^2$, set $s=Kq^2$. These parameters obey
--   $$q+1<s<N,\qquad3q+2\le N,\qquad2q\eta_{N,s,q}\le\frac18.$$
--   Here $\eta$ is the three-term quantity in Eq. (7). Thus the sample size used by the simulator satisfies all hypotheses of Lemma 3.3 and the precise error bound required in §4. The intermediate numerical estimate in the paragraph is not an additional target.
--
--   Differences from the source:
--   - encoding: K = 10^8 and real-valued differences in the error formula → a fixed natural K with coercions to real numbers in eta; reason: the sample size is an integer and the same positive denominators occur
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), §3.4, Eq. (8), PDF p. 13 (printed p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- §3.4, Eq. (8), PDF p.13 (printed p.11), including parameter admissibility. -/
theorem eq_8 {N q : ℕ} (hq : 1 ≤ q) (hN : K * q ^ 2 < N) :
    q + 1 < K * q ^ 2 ∧ K * q ^ 2 < N ∧ 3 * q + 2 ≤ N ∧
      2 * (q : ℝ) * eta N (K * q ^ 2) q ≤ (1 : ℝ) / 8 := by sorry

end PermSymQuery.Quadratic
