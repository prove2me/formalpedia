-- Prove2me | Theorems.Thm_SionMinimax_KneserFan_theorem_4_1_prime
-- name    : SionMinimax.KneserFan.theorem_4_1_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:52.297204+00:00
-- url     : https://prove2.me/theorems/adffe972-ef44-4892-91e2-03b843d890fa
-- title:
--   Theorem 4.1′, p. 175 — a finite Y ⊂ N beating every c > sup inf f gives sup inf f = inf sup f
-- statement:
--   Let $M$ and $N$ be arbitrary sets, not both empty, and let $f:M\times N\to\mathbb R$ be concave-convexlike (concavelike in $M$, convexlike in $N$, in the sense of Fan). Suppose that for every real number $c>\sup\inf f$ there is a finite set $Y\subset N$ such that for every $\mu\in M$ there is a $y\in Y$ with $f(\mu,y)<c$. Then
--   $$
--   \sup_{\mu\in M}\inf_{\nu\in N} f(\mu,\nu)\;=\;\inf_{\nu\in N}\sup_{\mu\in M} f(\mu,\nu),
--   $$
--   the two sides being extended real numbers.
--
--   The hypothesis is a finite-reduction condition: it is exactly what a compactness argument supplies in the Kneser–Fan theorem (Theorem 4.2), which the paper derives from this statement. The paper notes that 4.1′ itself is an immediate consequence of the finite-dimensional minimax theorem (Theorem 3.4; von Neumann's theorem).
--
--   **Formalization Note** The finite set $Y$ is a `Finset N` chosen after $c$ and before $\mu$, as on the page; $c$ ranges over the reals and is compared with the extended real $\sup\inf f$ through the coercion. The hypothesis "$M$ or $N$ is nonempty" is added: if $M=N=\varnothing$ the finite-set condition holds with $Y=\varnothing$, while $\sup\inf f=\sup\varnothing=-\infty$ and $\inf\sup f=\inf\varnothing=+\infty$, so the printed statement fails in that corner only. When exactly one of $M,N$ is empty both sides coincide ($-\infty$ if $M=\varnothing$, $+\infty$ if $N=\varnothing$), so those cases are kept.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 175 (PDF p. 6), Theorem 4.1′

import Mathlib
import Definitions.Def_SionMinimax_KneserFan_Concavelike

namespace SionMinimax.KneserFan
theorem theorem_4_1_prime {M N : Type*} (f : M → N → ℝ) (hf : ConcaveConvexlike f)
    (hne : Nonempty M ∨ Nonempty N)
    (hfin : ∀ c : ℝ, supInf f < (c : EReal) →
      ∃ Y : Finset N, ∀ μ : M, ∃ y ∈ Y, f μ y < c) :
    supInf f = infSup f := by sorry
end SionMinimax.KneserFan
