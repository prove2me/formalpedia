-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_deriv_a
-- name    : SampleDrivenOS.Linear.b9_deriv_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:30.00135+00:00
-- url     : https://prove2.me/theorems/534fa93f-10de-42ca-adf6-1ca2c77ef13d
-- title:
--   B.9, p. 36 — the derivative of $a(p)$, and $a'(p)=2\alpha^*(1-p)-b(p)+c(p)$
-- statement:
--   Let $s\in(0,1)$ and $p\in(0,1)$, and let $a$, $b$, $c$ be the functions of B.9 with parameter $s$:
--   $$a(p)=\sum_{i\ge1}\frac{\ln\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)}{i(i+1)}+s(2p-p^2),\quad b(p)=\frac1{p^2}\sum_{i\ge1}\frac{1}{i(i+1)\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)},$$
--   $$c(p)=\sum_{i\ge1}\frac{p^{i-1}-p^i}{\tfrac1{ps}-1+p^i(1+i(1-p))}.$$
--   Then $a$ is differentiable at $p$, and
--
--   1. its derivative is the term-by-term derivative
--   $$a'(p)=\sum_{i=1}^{\infty}\frac{-\tfrac1{p^2}+i(i+1)s(p^{i-1}-p^i)}{i(i+1)\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)}+2s(1-p);$$
--   2. equivalently, $a'(p)=2s(1-p)-b(p)+c(p)$.
--
--   This splits the derivative into a part bounded below ($b$) and a part bounded above ($c$), which the next steps of the proof of Theorem 9 estimate separately.
--
--   **Formalization Note** Both clauses are `HasDerivAt` statements for the function $p\mapsto a(p)$ on $\mathbb R$ at a point $p\in(0,1)$; differentiability of the series is part of the claim, not an assumption. Series are Lean `tsum`s with the index shifted by one.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 36, B.9 (Proof of Theorem 9), second display and the definitions of b(p) and c(p)

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_deriv_a (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (aB9 s)
        ((∑' i : ℕ, (-1 / p ^ 2 + (i + 1) * (i + 2) * s * (p ^ i - p ^ (i + 1))) /
            ((i + 1) * (i + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + (i + 1) * (1 - p)))))) +
          2 * s * (1 - p)) p ∧
      HasDerivAt (aB9 s) (2 * s * (1 - p) - bB9 s p + cB9 s p) p := by sorry

end SampleDrivenOS.Linear
