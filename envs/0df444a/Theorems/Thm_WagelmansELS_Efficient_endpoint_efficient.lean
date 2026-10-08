-- Prove2me | Theorems.Thm_WagelmansELS_Efficient_endpoint_efficient
-- name    : WagelmansELS.Efficient.endpoint_efficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:47.119357+00:00
-- url     : https://prove2.me/theorems/4e147ebe-4857-4fa3-bfcf-7a12af00a0ff
-- title:
--   Section 2: the envelope endpoints are efficient
-- statement:
--   For each $1\le i\le n$, the point at the largest plotted abscissa is $(D(i+1),G(i+1))$. In particular, for every later plotted period $t$ with the same abscissa, $G(i+1)\le G(t)$. The periods $i+1$ and $n+1$ are efficient:
--   $$i+1\in E_i,\qquad n+1\in E_i.$$
--
--   This identifies the two endpoint breakpoints and ensures the efficient-period set is nonempty.
--
--   **Formalization Note** If equal abscissae and heights occur, the earliest index is kept. The last demand is positive, so the sentinel is the only plotted period at abscissa zero.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S147, Section 2, sentence beginning “It follows that g(d_{i+1,n}) = G(i + 1)”; p. S148, endpoint breakpoints

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient

/-- Section 2, p. S147: the right endpoint of the envelope is `(D(i+1),G(i+1))`;
p. S148 declares the left endpoint `(0,0)` a breakpoint. -/
theorem endpoint_efficient (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (∀ t ∈ Finset.Ioc i (P.n + 1), i + 1 < t → P.D t = P.D (i + 1) →
      P.G (i + 1) ≤ P.G t) ∧
    P.IsEfficient i (i + 1) ∧ P.IsEfficient i (P.n + 1) := by sorry

end WagelmansELS.Efficient
