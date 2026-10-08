-- Prove2me | Theorems.Thm_WagelmansELS_Efficient_proposition_1
-- name    : WagelmansELS.Efficient.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:32.005913+00:00
-- url     : https://prove2.me/theorems/2feba90c-c3b1-43ea-8228-47be37475cbe
-- title:
--   Proposition 1: only efficient periods are needed in the minimum
-- statement:
--   For a period $1\le i\le n$, let $E_i$ be the efficient periods of the plotted points $(D(t),G(t))$. Then $E_i$ is nonempty and
--   $$\min_{i<t\le n+1}\{c_i[D(i)-D(t)]+G(t)\}
--   =\min_{t\in E_i}\{c_i[D(i)-D(t)]+G(t)\}.$$
--
--   Thus every excluded period is dominated for the candidate-cost calculation by an efficient period. This reduces the backward recursion to lower-envelope vertices.
--
--   **Formalization Note** The finite attained minima use `Finset.inf'`, whose domain is explicitly nonempty. The setup cost $f_i$ is absent from both sides because it is common to all candidates.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S148, Proposition 1

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_EfficientPeriods

namespace WagelmansELS.Efficient

/-- Proposition 1, p. S148: removing non-breakpoint periods leaves the minimum unchanged. -/
theorem proposition_1 (P : Instance) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (P.E i).Nonempty ∧
    ∀ h : (P.E i).Nonempty,
      (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
        (P.E i).inf' h (P.score i) := by sorry

end WagelmansELS.Efficient
