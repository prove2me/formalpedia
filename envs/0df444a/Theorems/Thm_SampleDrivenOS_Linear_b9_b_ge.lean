-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_b_ge
-- name    : SampleDrivenOS.Linear.b9_b_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:32.03261+00:00
-- url     : https://prove2.me/theorems/9be6cb8d-89e5-46c3-9760-2af7e6c00724
-- title:
--   B.9, p. 36 — $b(p)\ge 1/p$
-- statement:
--   Let $s\in(0,1)$ and $p\in(0,1)$, and let
--   $$b(p)=\frac1{p^2}\sum_{i=1}^{\infty}\frac{1}{i(i+1)\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)}.$$
--   Then
--   $$b(p)\ge\frac1p.$$
--
--   The reason given in the paper is that $s(1-p^i(1+i(1-p)))$ lies between $0$ and $s<1$, so every denominator is at most $i(i+1)/p$. This is the lower bound on $b$ used in the final estimate of $a'(p)$.
--
--   **Formalization Note** The series is a Lean `tsum` with the index shifted by one; it is summable for $s,p\in(0,1)$ since every denominator is at least $i(i+1)(1/p-s)>0$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 36, B.9 (Proof of Theorem 9), display bounding b(p)

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_b_ge (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 / p ≤ bB9 s p := by sorry

end SampleDrivenOS.Linear
