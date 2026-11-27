-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_kraft_necessity
-- name    : PrivateContinualCounting.Kraft.kraft_necessity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:39.157796+00:00
-- url     : https://prove2.me/theorems/6eb274b0-0623-5def-987b-5b1cc86aeb8d
-- title:
--   Kraft necessity for real LTI counters (§3.2)
-- statement:
--   This is the necessity in Theorem 1.1(ii), in the generality of §3.2, where the envelope is only assumed nondecreasing.
--
--   Let $m\ge1$ and let $(l_j)_{j\ge0}\subset\mathbb R^{1\times m}$ and $(r_k)_{k\ge0}\subset\mathbb R^{m}$ be real LTI factors: $\sum_{j=0}^{s}l_jr_{s-j}=1$ for every $s\ge0$, and $\Delta^2=\sum_{k\ge0}\|r_k\|_2^2<\infty$. Write $E_t=\sum_{j<t}\|l_j\|_2^2$ and let $v_t=\Delta^2E_t$ be the normalized variance. Let $g:[1,\infty)\to[1,\infty)$ be nondecreasing. If there is a constant $C>0$ with
--
--   $$v_t\le C(\ln t)^2\,g(\ln t)\qquad\text{for all integers }t\ge3,$$
--
--   then
--
--   $$\sum_{k\ge0}\frac{1}{g(2^k)}<\infty .$$
--
--   No doubling condition on $g$ is needed. This is the half of the Kraft law saying that time invariance costs at least a Kraft-summable factor over $(\ln t)^2$.
--
--   **Formalization Note** The factors are `LTIData ℝ m` with `IsLTI` (which includes $m>0$); the envelope hypothesis is `HasEnvelope d.variance g`, whose positive constant is fixed before all times.
-- source:
--   Kisung Park, Sharp Limits of Time Invariance in Private Continual Counting, STOC 2027 submission #86 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/86.pdf, p. 1 (PDF p. 3), Theorem 1.1(ii), 'only if' direction; p. 8 (PDF p. 10), §3.2, where g:[1,∞)→[1,∞) is only assumed nondecreasing.

import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- §3.2: Kraft necessity for real scalar/vector LTI factors, for every g:[1,∞)→[1,∞)
that is only assumed nondecreasing. -/
theorem kraft_necessity (m : ℕ) (d : LTIData ℝ m) (hd : IsLTI d) (g : ℝ → ℝ)
    (hg1 : ∀ u : ℝ, 1 ≤ u → 1 ≤ g u) (hgm : MonotoneOn g (Set.Ici 1))
    (henv : HasEnvelope d.variance g) : KraftCondition g := by sorry

end PrivateContinualCounting.Kraft
