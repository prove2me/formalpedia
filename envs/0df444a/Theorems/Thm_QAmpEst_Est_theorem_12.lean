-- Prove2me | Theorems.Thm_QAmpEst_Est_theorem_12
-- name    : QAmpEst.Est.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:44.481167+00:00
-- url     : https://prove2.me/theorems/237c190d-621d-43bf-af21-f6056d59d6ee
-- title:
--   Theorem 12 (Amplitude Estimation), p. 19 — |ã − a| ≤ 2πk√(a(1−a))/M + k²π²/M² w.p. ≥ 8/π² (k = 1), > 1 − 1/(2(k−1)) (k ≥ 2); exact for a = 0, and for a = 1 with M even
-- statement:
--   Let $\mathcal A$ be a unitary on a finite-dimensional Hilbert space with computational basis indexed by $\iota$, let $\chi : \iota \to \{0,1\}$ mark the good basis states, and let $a = \langle\Psi_1|\Psi_1\rangle$ be the probability that measuring $\mathcal A|0\rangle$ gives a good state. Let $M \ge 1$, and let $\tilde a = \sin^2(\pi y/M)$ be the output of $\mathbf{Est\_Amp}(\mathcal A,\chi,M)$, where $y$ is the measured value of the first register. For every positive integer $k$, the event
--   $$|\tilde a - a| \le 2\pi k\,\frac{\sqrt{a(1-a)}}{M} + k^2\frac{\pi^2}{M^2}$$
--   has probability
--
--   1. at least $8/\pi^2$ when $k = 1$, and
--   2. greater than $1 - \frac{1}{2(k-1)}$ when $k \ge 2$.
--
--   Moreover,
--
--   3. if $a = 0$ then $\tilde a = 0$ with certainty, and
--   4. if $a = 1$ and $M$ is even, then $\tilde a = 1$ with certainty.
--
--   This is the main estimation result of the paper: $M$ applications of $\mathbf Q$ give an estimate of $a$ with additive error of order $\sqrt{a(1-a)}/M$, a quadratic improvement over classical sampling.
--
--   **Formalization Note** The probability of an event is the sum, over the outcomes $y$ in it, of $\sum_z |\langle y,z|\psi_{\mathrm{final}}\rangle|^2$, where $\psi_{\mathrm{final}} = (F_M^{-1}\otimes I)\Lambda_M(\mathbf Q)(F_M\otimes I)|0\rangle\mathcal A|0\rangle$. The clause "it uses exactly $M$ evaluations of $f$" is not formalized: the matrix model has no oracle whose calls could be counted. $0 \le \tilde a \le 1$ holds by construction. No restriction $0 < a < 1$ and no lower bound on $M$ is assumed.
-- source:
--   arXiv:quant-ph/0005055v1, Theorem 12, p. 19; Algorithm Est_Amp, p. 18

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Theorem 12 (Amplitude Estimation), arXiv:quant-ph/0005055v1, p. 19: for any positive
integer `k`, the output `ã = sin²(πy/M)` of `Est_Amp(A, χ, M)` satisfies
`|ã − a| ≤ 2πk√(a(1 − a))/M + k²π²/M²` with probability at least `8/π²` when `k = 1` and with
probability greater than `1 − 1/(2(k − 1))` for `k ≥ 2`. If `a = 0` then `ã = 0` with
certainty, and if `a = 1` and `M` is even, then `ã = 1` with certainty.
(The query count "exactly `M` evaluations of `f`" is not formalized.) -/
theorem theorem_12 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (M : ℕ) (hM : 0 < M) (k : ℕ) (hk : 1 ≤ k) :
    let a := succProb A χ z0
    let P := outcomeProb M A χ z0
    let E := Finset.univ.filter (fun y : Fin M =>
      |estimate M y - a| ≤
        2 * π * (k : ℝ) * Real.sqrt (a * (1 - a)) / (M : ℝ) + (k : ℝ) ^ 2 * π ^ 2 / (M : ℝ) ^ 2)
    (k = 1 → 8 / π ^ 2 ≤ ∑ y ∈ E, P y) ∧
      (2 ≤ k → 1 - 1 / (2 * ((k : ℝ) - 1)) < ∑ y ∈ E, P y) ∧
      (a = 0 → ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 0), P y = 1) ∧
      (a = 1 → Even M →
        ∑ y ∈ Finset.univ.filter (fun y : Fin M => estimate M y = 1), P y = 1) := by sorry

end QAmpEst.Est
