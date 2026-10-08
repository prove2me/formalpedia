-- Prove2me | Theorems.Thm_SionMinimax_KneserFan_theorem_4_2
-- name    : SionMinimax.KneserFan.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:55.610986+00:00
-- url     : https://prove2.me/theorems/95f6bb86-7632-4ab2-8e10-0ff97efc43fa
-- title:
--   Theorem 4.2 (Kneser, Fan), p. 175 — M compact, f concave-convexlike and u.s.c. in μ: sup inf f = inf sup f
-- statement:
--   **Kneser–Fan minimax theorem.** Let $M$ be a compact topological space and $N$ an arbitrary set, not both empty, and let $f:M\times N\to\mathbb R$ be concave-convexlike: concavelike in $M$ and convexlike in $N$ in the sense of Fan. If for each $\nu\in N$ the function $\mu\mapsto f(\mu,\nu)$ is upper semicontinuous on $M$, then
--   $$
--   \sup_{\mu\in M}\inf_{\nu\in N} f(\mu,\nu)\;=\;\inf_{\nu\in N}\sup_{\mu\in M} f(\mu,\nu),
--   $$
--   in the extended reals.
--
--   This is Fan's generalization of Kneser's minimax theorem from concave-convex functions on convex sets to concave-convexlike functions on spaces without linear structure. It is not a special case of Sion's quasi-concave-convex minimax theorem, since the two classes of functions are independent.
--
--   **Formalization Note** $M$ carries an arbitrary topology with `CompactSpace M` (no Hausdorff assumption); $N$ has no structure. Upper semicontinuity is Mathlib's `UpperSemicontinuous` on $M$. The values $\sup\inf f$ and $\inf\sup f$ are computed in `EReal`. The hypothesis "$M$ or $N$ is nonempty" is added because with $M=N=\varnothing$ every other hypothesis holds while $\sup\inf f=-\infty\neq+\infty=\inf\sup f$; when exactly one of them is empty both sides agree.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 175 (PDF p. 6), Theorem 4.2 (Kneser, Fan)

import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_2 {M N : Type*} [TopologicalSpace M] [CompactSpace M]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (husc : ∀ ν : N, UpperSemicontinuous (fun μ : M => f μ ν)) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan
