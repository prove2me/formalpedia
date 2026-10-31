-- Prove2me | Theorems.Thm_SQMeanEstimation_ringInf_estimate
-- name    : SQMeanEstimation.ringInf_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:55.772325+00:00
-- url     : https://prove2.me/theorems/e2046b2e-f7be-49e6-a202-fb5e63c496bc
-- title:
--   Proof of Theorem 3.15 — $\bar w^\infty=\mathbf E[R_\infty(\mathbf w)]$ to $\ell_q$ error $\varepsilon'$ (corrected: $\mathrm{VSTAT}((4/\varepsilon')^2)$, per-coordinate for $\varepsilon'\le2$)
-- statement:
--   Let $d\ge1$, $q\in(1,2)$ and $k=\lfloor\log_2(d)/q\rfloor-2$. Then
--
--   1. $2^{-k-1}\le2^{1-\lfloor\log_2(d)/q\rfloor}\le4d^{-1/q}$;
--   2. for every $\varepsilon'>0$ there is a non-adaptive SQ algorithm with $d$ queries such that, for every Borel probability distribution $\mu$ on $\mathbb R^d$ supported on $B_q^d$ and every answer vector $v$ that $\mathrm{VSTAT}_\mu((4/\varepsilon')^2)$ may return, its output $\tilde w^\infty$ satisfies, with $\bar w^\infty=\mathbf E_\mu[R_\infty(\mathbf w)]$,
--   $$
--   \|\bar w^\infty-\tilde w^\infty\|_q\le\varepsilon',\qquad\text{and, if }\varepsilon'\le2,\quad |\tilde w^\infty_i-\bar w^\infty_i|\le\varepsilon'\,d^{-1/q}\ \text{ for every }i.
--   $$
--
--   This is the last of the $2k+3$ estimates whose errors add up to $\varepsilon$ in the proof of Theorem 3.15: the coordinates of $R_\infty$ are at most $4d^{-1/q}$ in absolute value, so coordinate-wise estimation suffices.
--
--   Differences from the source:
--   - correction: VSTAT(1/(4ε′)²) → VSTAT((4/ε′)²); reason: the printed parameter is false: d = 7, q = 3/2 (k = −1, so R_∞ keeps every coordinate of the ball), ε′ = 1/5 gives VSTAT(1/0.64) with tolerance ≥ 0.64; the answers E_{δ₀}φᵢ are valid for both δ₀ and 0.36δ₀ + 0.64δ_{e₁}, whose means are at ℓq distance 0.64 > 2ε′, so no output is ε′-close to both
--   - correction: coordinate-wise accuracy ε′·d^{−1/q} for every ε′ > 0 → only for ε′ ≤ 2 (the ℓq clause is kept for every ε′ > 0); reason: false for large ε′: d = 7, q = 3/2, ε′ = 3 gives VSTAT(16/9) with tolerance ≥ 9/16, and the common answers (φ(−e₁) + φ(e₁))/2 are valid for δ_{−e₁} and δ_{e₁}, whose first coordinates −1 and 1 cannot both be within 3·7^{−2/3} ≈ 0.82 of one output; in the proof of Theorem 3.15 ε′ ≤ ε and only ε < 1 is nontrivial
--   - reading: log → Real.logb 2; reason: the ring thresholds are powers of 2, and the step 2^{1−⌊log(d)/q⌋} ≤ 4d^{−1/q} holds only in base 2
--   - generalization: we can obtain an estimate using VSTAT → there is a deterministic non-adaptive algorithm with d queries that succeeds against every valid answer vector; reason: such an algorithm is a statistical query algorithm, so the statement implies the source's claim
--   - encoding: d (implicitly ≥ 1) → hypothesis 1 ≤ d; reason: d^{−1/q} is undefined at d = 0; only the degenerate space ℝ⁰ is excluded
--   - encoding: w supported on B_q^d; E; VSTAT(n) with n an integer → probability measure μ with lqNorm q w ≤ 1 μ-a.s.; Bochner integral; real parameter (4/ε′)²; reason: the distribution of the random variable; the parameter is not an integer
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.18, paragraph "Finally, to estimate"

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_NonadaptiveSQ
import Definitions.Def_SQMeanEstimation_ValidVSTATAnswers
import Definitions.Def_SQMeanEstimation_ringInf
import Definitions.Def_SQMeanEstimation_ringDepth

open MeasureTheory

namespace SQMeanEstimation

/-- **Estimate of the remainder `w̄^∞ = E[R_∞(w)]` (corrected: VSTAT((4/ε′)²), coordinate bound for ε′ ≤ 2).**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, p.18: "Finally, to estimate, w̄^∞ ≐ E[R_∞(w)] we
observe that 2^{−k−1} ≤ 2^{1−⌊log(d)/q⌋} ≤ 4d^{−1/q}. Now using VSTAT(1/(4ε′)²) we can obtain an
estimate of each coordinate of w̄^∞ with accuracy ε′ · d^{−1/q}. In particular, the estimate w̃^∞
obtained in this way satisfies ‖w̄^∞ − w̃^∞‖_q ≤ ε′." Here `k = ⌊log(d)/q⌋ − 2` (p.17).

For `d ≥ 1`, `q ∈ (1, 2)` and `k = ⌊log₂(d)/q⌋ − 2`:
1. `2^{−k−1} ≤ 2^{1−⌊log₂(d)/q⌋} ≤ 4d^{−1/q}`;
2. for every `ε′ > 0` there is a non-adaptive SQ algorithm with `d` queries such that, for
   every Borel probability measure `μ` supported on `Bᵈ_q` and every answer vector valid for
   VSTAT_μ((4/ε′)²), its output `w̃^∞` satisfies `‖E_μ[R_∞(w)] − w̃^∞‖_q ≤ ε′`, and, when
   `ε′ ≤ 2`, also `|w̃^∞ᵢ − (E_μ[R_∞(w)])ᵢ| ≤ ε′·d^{−1/q}` for every `i`.

**Formalization Note.** The printed parameter `1/(4ε′)²` is corrected to `(4/ε′)²`, and the
coordinate-wise clause is restricted to `ε′ ≤ 2` (the ℓq clause holds for every `ε′ > 0`): at
`ε′ = 1/5` the printed oracle has tolerance `≥ 0.64` and cannot separate `δ₀` from
`0.36δ₀ + 0.64δ_{e₁}` (`d = 7`, `q = 3/2`); at `ε′ = 3` the oracle VSTAT(16/9) cannot separate
`δ_{−e₁}` from `δ_{e₁}` in coordinate 1 to accuracy `3·7^{−2/3}`. `log` is `Real.logb 2`, `k` is
`ringDepth d q : ℤ`, powers of 2 with integer exponent are `zpow`. -/
theorem ringInf_estimate {d : ℕ} (hd : 1 ≤ d) (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    ((2 : ℝ) ^ (-ringDepth d q - 1) ≤ (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) ∧
      (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) ≤ 4 * (d : ℝ) ^ (-1 / q)) ∧
    ∀ ε' : ℝ, 0 < ε' →
      ∃ A : NonadaptiveSQ d d,
        ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, lqNorm q w ≤ 1) →
          ∀ v : Fin d → ℝ, ValidVSTATAnswers μ ((4 / ε') ^ 2) A v →
            (ε' ≤ 2 → ∀ i, |A.output v i - (∫ w, ringInf (ringDepth d q) w ∂μ) i| ≤
                ε' * (d : ℝ) ^ (-1 / q)) ∧
            lqNorm q ((∫ w, ringInf (ringDepth d q) w ∂μ) - A.output v) ≤ ε' := by sorry

end SQMeanEstimation
