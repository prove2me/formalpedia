-- Prove2me | Theorems.Thm_SionMinimax_KneserFan_theorem_4_1
-- name    : SionMinimax.KneserFan.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:52.279332+00:00
-- url     : https://prove2.me/theorems/5e57dcdf-78bb-4f7f-bdc8-c62fdd8924bc
-- title:
--   Theorem 4.1, p. 175 — a finite X ⊂ M beating every c < inf sup f gives sup inf f = inf sup f
-- statement:
--   Let $M$ and $N$ be arbitrary sets, not both empty, and let $f:M\times N\to\mathbb R$ be concave-convexlike. Suppose that for every real number $c<\inf\sup f$ there is a finite subset $X\subset M$ such that for every $\nu\in N$ there is an $x\in X$ with $f(x,\nu)>c$. Then
--   $$
--   \sup_{\mu\in M}\inf_{\nu\in N} f(\mu,\nu)\;=\;\inf_{\nu\in N}\sup_{\mu\in M} f(\mu,\nu),
--   $$
--   in the extended reals.
--
--   This is the dual of Theorem 4.1′, with the finite reduction made on the maximizing side; it yields Theorem 4.2′ (compact $N$, lower semicontinuity in $\nu$) in the same way as 4.1′ yields 4.2.
--
--   **Formalization Note** The finite set $X$ is a `Finset M` chosen after $c$ and before $\nu$; $c$ is real and compared with the extended real $\inf\sup f$ through the coercion. The hypothesis "$M$ or $N$ is nonempty" is added: if $M=N=\varnothing$ the finite-set condition holds with $X=\varnothing$ while $\sup\inf f=-\infty\neq+\infty=\inf\sup f$.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 175 (PDF p. 6), Theorem 4.1

import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_1 {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, (c : EReal) < infSup f →
      ∃ X : Finset M, ∀ ν : N, ∃ x ∈ X, c < f x ν) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan
