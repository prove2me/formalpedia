-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_kraft_sufficiency
-- name    : PrivateContinualCounting.Kraft.kraft_sufficiency
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:38.911799+00:00
-- url     : https://prove2.me/theorems/902a5c67-b250-4138-a998-81bb53ca827e
-- title:
--   Kraft sufficiency: a real scalar LTI counter realises $(\ln t)^2 g(\ln t)$
-- statement:
--   This is the sufficiency in Theorem 1.1(ii): every Kraft-admissible envelope is realised by a real scalar time-invariant counter.
--
--   Let $g:[1,\infty)\to[1,\infty)$ be nondecreasing with $g(2u)\le D\,g(u)$ for some $D\ge1$ and all $u\ge1$, and assume the Kraft condition $\sum_{k\ge0}1/g(2^k)<\infty$. Then there are real scalar LTI factors $(l_j)_{j\ge0}$, $(r_k)_{k\ge0}$ with $\sum_{j=0}^{s}l_jr_{s-j}=1$ for every $s\ge0$ and $\Delta^2=\sum_{k\ge0}r_k^2<\infty$, and a constant $C>0$, such that the normalized variance $v_t=\Delta^2\sum_{j<t}l_j^2$ satisfies
--
--   $$v_t\le C(\ln t)^2\,g(\ln t)\qquad\text{for all integers }t\ge3.$$
--
--   Together with the necessity half, this shows that Kraft summability is exactly the price of time invariance for prefix sums. The source builds the counter from the outer function of a spectral weight (§3.3); the statement here asserts the existence of the counter and its uniform envelope.
--
--   **Formalization Note** The counter is an `LTICounter 1`, that is `LTIData ℝ 1` with `IsLTI`; `HasEnvelope` fixes one positive constant for all $t\ge3$.
-- source:
--   Kisung Park, Sharp Limits of Time Invariance in Private Continual Counting, STOC 2027 submission #86 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/86.pdf, p. 1 (PDF p. 3), Theorem 1.1(ii), 'if' direction and 'If K(g) holds, a scalar counter with real coefficients suffices'; p. 8 (PDF p. 10), §3.3.

import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Theorem 1.1(ii), sufficiency: under the Kraft condition a real scalar LTI counter
with bounded sensitivity realizes the envelope (ln t)^2 g(ln t). -/
theorem kraft_sufficiency (g : ℝ → ℝ) (hg : IsEnvelope g) (hK : KraftCondition g) :
    ∃ M : LTICounter 1, HasEnvelope M.val.variance g := by sorry

end PrivateContinualCounting.Kraft
