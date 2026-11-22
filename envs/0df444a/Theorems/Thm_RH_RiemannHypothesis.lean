-- Prove2me | Theorems.Thm_RH_RiemannHypothesis
-- name    : RH.RiemannHypothesis
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:01:50.390803+00:00
-- url     : https://prove2.me/theorems/4ef51181-b0c5-4e7a-8205-150a8845dfb3
-- title:
--   Riemann hypothesis
-- statement:
--   **The Riemann hypothesis**, stated exactly as Mathlib's proposition `RiemannHypothesis`.
--
--   Let $\zeta$ denote the Riemann zeta function, extended to all of $\mathbb{C}$. Every zero $s$ of $\zeta$ that is not a trivial zero satisfies $\operatorname{Re}(s) = \tfrac12$. Precisely: for every $s \in \mathbb{C}$ with $\zeta(s) = 0$, if $s$ is not of the form $-2(n+1)$ for a natural number $n$ (the trivial zeros $-2, -4, -6, \dots$) and $s \neq 1$, then $\operatorname{Re}(s) = \tfrac12$.
--
--   The condition $s \neq 1$ appears because Mathlib's `riemannZeta` is a total function that assigns a conventional value at the pole $s = 1$. This is an open problem.
-- source:
--   Mathlib, Mathlib.NumberTheory.LSeries.RiemannZeta, definition RiemannHypothesis. B. Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse (1859).

import Mathlib

namespace RH
theorem RiemannHypothesis : _root_.RiemannHypothesis := by sorry
end RH
