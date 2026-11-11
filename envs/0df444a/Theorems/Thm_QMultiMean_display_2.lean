-- Prove2me | Theorems.Thm_QMultiMean_display_2
-- name    : QMultiMean.display_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:09:47.21293+00:00
-- url     : https://prove2.me/theorems/5cc7c26a-4fb6-4af9-b43a-ad6749a9ec02
-- title:
--   Display (2) — $a_j\le c^{-1/2}2^{j/2}\sqrt{\mathbb E\|Y\|_2^2}$
-- statement:
--   Let $Y$ be a finite random variable over $\mathbb R^d$, let $Q$ be the quantile function of $\|Y\|_2$, let $c\in(0,1)$ and $j\ge0$. If a real $a_j$ satisfies $Q(2^{-j})\le a_j\le Q(c2^{-j})$, then
--   $$a_j\le c^{-1/2}\,2^{j/2}\sqrt{\mathbb E[\|Y\|_2^2]} .$$
--
--   It bounds the slicing levels of Algorithm 2 and hence the error that each slice contributes.
--
--   Differences from the source:
--   - generalization: Y = X − η, the centred variable of Algorithm 2 → any finite random variable Y over ℝ^d; reason: the display's argument uses only that Y is a finite random variable; X − η is one
--   - generalization: c the constant of Proposition 2.9 (printed as "Theorem 2.9") → any c ∈ (0, 1); reason: the display's argument uses only c ∈ (0, 1)
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.12, proof of Theorem 3.4, display (2)

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_quantile

set_option autoImplicit false

namespace QMultiMean

/-- Display (2) in the proof of Theorem 3.4 of Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2,
p.12: if `Q(2^{−j}) ≤ a_j ≤ Q(c2^{−j})`, where `Q` is the quantile function of `‖Y‖₂`, then
`a_j ≤ c^{−1/2} 2^{j/2} √E[‖Y‖₂²]`.

**Formalization Note.** Stated for every finite random variable `Y` over `ℝ^d` (in the proof,
`Y = X − η`), every `c ∈ (0, 1)` (in the proof, the constant of Proposition 2.9, which the text calls
"Theorem 2.9") and every real `a` between the two quantiles. -/
theorem display_2 (d N : ℕ) (P : Fin (N + 1) → ℝ) (Y : Fin (N + 1) → Vec d) (hP : IsPMF P)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (j : ℕ) (a : ℝ)
    (hlo : quantile P (fun ω => ‖Y ω‖) (1 / 2 ^ j) ≤ a)
    (hhi : a ≤ quantile P (fun ω => ‖Y ω‖) (c * (1 / 2 ^ j))) :
    a ≤ c ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ ((j : ℝ) / 2) *
      Real.sqrt (expect P (fun ω => ‖Y ω‖ ^ 2)) := by sorry

end QMultiMean
