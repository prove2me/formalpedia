-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_proposition_4_a_strict
-- name    : VolDisclosure.Evidence.proposition_4_a_strict
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T23:04:33.258666+00:00
-- url     : https://prove2.me/theorems/a837d9ad-b657-42f8-88e0-3c6cee1b6a0a
-- title:
--   Proposition 4(a), p. 20, corrected, strict part — s(v;π) < s(v;π') for v^1(π) < v < v̄
-- statement:
--   Fix parameters $h > l > 0$, $p \in (0,1)$, $r \in (0,1)$, $\lambda \in (0,1]$, and evidence probabilities $0 \le \pi < \pi' < 1$. Let $s = s(\cdot\,;\pi)$ and $s' = s(\cdot\,;\pi')$ be the firm values (fixed points in $\mathcal F$ of the Bellman operator (T), p. 37) for $\pi$ and $\pi'$. Then for every promised utility $v$ with
--   $$
--   v^1(\pi) = \frac{\hat r\,\bar v}{1+\hat r} < v < \bar v = \frac{(1+r)p\delta}{r}, \qquad \hat r = \frac{r}{1-(1-p)\pi},
--   $$
--   one has
--   $$
--   s(v) < s'(v).
--   $$
--
--   This is the strict half of the corrected Proposition 4(a): greater availability of evidence strictly raises firm value above the first termination threshold of the lower evidence probability and below the payout boundary. The weak inequality $s \le s'$ on $\mathbb R_+$ holds everywhere and is not part of this statement.
--
--   **Formalization Note.** The strict inequality is restricted to $(v^1(\pi), \bar v)$ as in the corrected statement of `VolDisclosure.Evidence.proposition_4_a`: when $p \le r$ the two firm values coincide on $[0, v^1(\pi)]$, and both equal $s^*$ for $v \ge \bar v$.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), https://files.webservices.illinois.edu/6984/voluntarydisclosure.pdf, p. 20, Proposition 4(a) (strict part, corrected as in VolDisclosure.Evidence.proposition_4_a); proof p. 41, envelope condition (A.20)

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition 4(a) (p. 20; proof p. 41), corrected, strict part: for `0 ≤ π < π' < 1`, the
firm value is strictly higher under the higher evidence probability at every promised utility
`v` with `v¹(π) < v < v̄`. -/
theorem proposition_4_a_strict (P : Params) (hP : P.Standing) (π π' : ℝ) (hπ0 : 0 ≤ π)
    (hππ' : π < π') (hπ'1 : π' < 1) (s s' : ℝ → ℝ) (hs : IsValue P π s) (hs' : IsValue P π' s')
    (v : ℝ) (hv1 : P.v1 π < v) (hv2 : v < P.vBar) :
    s v < s' v := by sorry

end VolDisclosure.Evidence
