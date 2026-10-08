-- Prove2me | Theorems.Thm_SionMinimax_KneserFan_theorem_4_2_prime
-- name    : SionMinimax.KneserFan.theorem_4_2_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:04.567981+00:00
-- url     : https://prove2.me/theorems/099f0cac-bae6-498c-ab9d-fdb0134e77af
-- title:
--   Theorem 4.2′, p. 175 — N compact, f concave-convexlike and l.s.c. in ν: sup inf f = inf sup f
-- statement:
--   Let $M$ be an arbitrary set and $N$ a compact topological space, not both empty, and let $f:M\times N\to\mathbb R$ be concave-convexlike. If for each $\mu\in M$ the function $\nu\mapsto f(\mu,\nu)$ is lower semicontinuous on $N$, then
--   $$
--   \sup_{\mu\in M}\inf_{\nu\in N} f(\mu,\nu)\;=\;\inf_{\nu\in N}\sup_{\mu\in M} f(\mu,\nu),
--   $$
--   in the extended reals.
--
--   This is the companion of the Kneser–Fan theorem (Theorem 4.2) with the roles of the two players exchanged: compactness and semicontinuity are required on the minimizing side.
--
--   **Formalization Note** $N$ carries an arbitrary topology with `CompactSpace N`; no Hausdorff or linear structure is assumed, and $M$ has no structure at all. The hypothesis "$M$ or $N$ is nonempty" is added because with $M=N=\varnothing$ every other hypothesis holds while $\sup\inf f=-\infty\neq+\infty=\inf\sup f$.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 175 (PDF p. 6), Theorem 4.2′

import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_2_prime {M N : Type*} [TopologicalSpace N] [CompactSpace N]
    (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hlsc : ∀ μ : M, LowerSemicontinuous (fun ν : N => f μ ν)) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan
