-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_eq_B14
-- name    : QSVTPhaseEst.BitSearch.eq_B14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:32.85461+00:00
-- url     : https://prove2.me/theorems/fe63acc5-aa85-4bec-a7d4-e4d5ed245b94
-- title:
--   (B14), p. 30 — |cos(πx)| lies in the Δ-region iff π|x| lies in the two arccos intervals
-- statement:
--   Let $0 \le \Delta \le 2 - \sqrt2$ and $x \in \mathbb R$ with $|x| \le 1$. Then $|\cos(\pi x)| \in \bigl[\tfrac1{\sqrt2} - \tfrac\Delta2,\ \tfrac1{\sqrt2} + \tfrac\Delta2\bigr]$ if and only if
--   $$\pi|x| \in \Bigl[\arccos\bigl(\tfrac1{\sqrt2} + \tfrac\Delta2\bigr), \arccos\bigl(\tfrac1{\sqrt2} - \tfrac\Delta2\bigr)\Bigr] \cup \Bigl[\arccos\bigl(-\tfrac1{\sqrt2} + \tfrac\Delta2\bigr), \arccos\bigl(-\tfrac1{\sqrt2} - \tfrac\Delta2\bigr)\Bigr].$$
--
--   Applied to $x = 0.\varphi_{[j+1:]} - \theta$, by (65) this decides whether the singular value $\sigma^j$ of iteration $j$ falls in the Δ-region in terms of the distance between the remaining digits of $\varphi$ and the current $\theta$.
--
--   **Formalization Note** The page states the equivalence for $x = 0.\varphi_{[j+1:]} - \theta$, which lies in $(-1/2, 1)$; the statement is for any $|x| \le 1$, so that $\pi|x| \in [0, \pi]$. The hypothesis $\Delta \le 2 - \sqrt2$ keeps every argument of $\arccos$ in $[-1, 1]$ (Lean's `Real.arccos` is clamped outside it); it is implied by the threshold of Theorem 8.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 30, (B14) (Appendix B 2)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem eq_B14 (Δ x : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 2 - Real.sqrt 2) (hx : |x| ≤ 1) :
    InDeltaRegion Δ |Real.cos (Real.pi * x)| ↔
      Real.pi * |x| ∈
        Set.Icc (Real.arccos (1 / Real.sqrt 2 + Δ / 2)) (Real.arccos (1 / Real.sqrt 2 - Δ / 2)) ∪
        Set.Icc (Real.arccos (-1 / Real.sqrt 2 + Δ / 2))
          (Real.arccos (-1 / Real.sqrt 2 - Δ / 2)) := by sorry

end QSVTPhaseEst.BitSearch
