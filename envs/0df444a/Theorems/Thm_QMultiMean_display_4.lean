-- Prove2me | Theorems.Thm_QMultiMean_display_4
-- name    : QMultiMean.display_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:09:35.426214+00:00
-- url     : https://prove2.me/theorems/c13ac625-e105-4c78-9db0-daad9e157a8f
-- title:
--   Display (4) — the tail mean $\mathbb E[\![Y]\!]_{a_k}^{+\infty}$ is at most $\sqrt{\mathbb E\|Y\|_2^2}/2^{k/2}$
-- statement:
--   Let $Y$ be a finite random variable over $\mathbb R^d$ and $Q$ the quantile function of $\|Y\|_2$. Let $k\ge0$ and $a_k\ge0$ with $a_k\ge Q(2^{-k})$. Then the mean of the truncated tail $[\![Y]\!]_{a_k}^{+\infty}$ satisfies
--   $$\big\|\mathbb E[\![Y]\!]_{a_k}^{+\infty}\big\|_\infty\le\big\|\mathbb E[\![Y]\!]_{a_k}^{+\infty}\big\|_2\le\sqrt{\mathbb E[\|Y\|_2^2]\,\Pr[\|Y\|_2>a_k]}\le\frac{\sqrt{\mathbb E[\|Y\|_2^2]}}{2^{k/2}} .$$
--
--   This bounds the part of the mean of $Y$ that Algorithm 2 does not estimate.
--
--   Differences from the source:
--   - reading: ‖⟦Y⟧_{a_k}^{+∞}‖∞ ≤ ‖⟦Y⟧_{a_k}^{+∞}‖₂ ≤ … (norms of the truncated random variable) → the same chain for the norms of the mean E[⟦Y⟧_{a_k}^{+∞}]; reason: pointwise the printed chain is false (a value of ⟦Y⟧ can exceed √E‖Y‖₂²/2^{k/2}); the proof uses it as the untracked part of µ_Y, and the Cauchy–Schwarz step is for the expectation
--   - reading: a_k the quantile estimate of step 4a → any a_k with a_k ≥ Q(2^{−k}); reason: the bound uses only Q(2^{−k}) ≤ a_k, which the proof states for the estimates (and which forces a_k ≥ 0)
--   - generalization: Y = X − η, the centred variable of Algorithm 2 → any finite random variable Y over ℝ^d; reason: the display's argument uses only that Y is a finite random variable; X − η is one
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.13, proof of Theorem 3.4, display (4)

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_quantile

set_option autoImplicit false

namespace QMultiMean

/-- Display (4) in the proof of Theorem 3.4 of Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2,
p.13: the truncated random variable `⟦Y⟧_{a_k}^{+∞}` satisfies
`‖⟦Y⟧_{a_k}^{+∞}‖∞ ≤ ‖⟦Y⟧_{a_k}^{+∞}‖₂ ≤ √(E[‖Y‖₂²] Pr[‖Y‖₂ > a_k]) ≤ √E[‖Y‖₂²] / 2^{k/2}`.

**Formalization Note.** Read as a statement about the mean `E[⟦Y⟧_{a_k}^{+∞}]`, the part of
`µ_Y` that the estimate does not track (the printed norms of a random vector cannot be bounded by a
constant pointwise, and the Cauchy–Schwarz step is for the expectation). `a` stands for `a_k`,
with `a ≥ Q(2^{−k})` (`Q` the quantile function of `‖Y‖₂`), as the quantile estimates of step 4a
give; this forces `a ≥ 0`, since `Q(2^{−k}) ≥ 0`. The whole chain is stated, as a conjunction. Stated for every finite random variable `Y` over
`ℝ^d` (in the proof, `Y = X − η`). -/
theorem display_4 (d N : ℕ) (P : Fin (N + 1) → ℝ) (Y : Fin (N + 1) → Vec d) (hP : IsPMF P)
    (k : ℕ) (a : ℝ) (hq : quantile P (fun ω => ‖Y ω‖) (1 / 2 ^ k) ≤ a) :
    supNorm (mean P (fun ω => truncTop a (Y ω))) ≤ ‖mean P (fun ω => truncTop a (Y ω))‖ ∧
    ‖mean P (fun ω => truncTop a (Y ω))‖ ≤
      Real.sqrt (expect P (fun ω => ‖Y ω‖ ^ 2) * prob P (fun ω => a < ‖Y ω‖)) ∧
    Real.sqrt (expect P (fun ω => ‖Y ω‖ ^ 2) * prob P (fun ω => a < ‖Y ω‖)) ≤
      Real.sqrt (expect P (fun ω => ‖Y ω‖ ^ 2)) / (2 : ℝ) ^ ((k : ℝ) / 2) := by sorry

end QMultiMean
