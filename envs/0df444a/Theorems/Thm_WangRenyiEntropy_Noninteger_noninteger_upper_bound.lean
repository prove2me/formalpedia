-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_noninteger_upper_bound
-- name    : WangRenyiEntropy.Noninteger.noninteger_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:27.121218+00:00
-- url     : https://prove2.me/theorems/c13acc3e-7dfd-4c50-b7a4-c000e9a11037
-- title:
--   Theorem 4.1 — success of the exact estimator (20)–(22)
-- statement:
--   Fix any positive noninteger $\alpha$, the uniform constant $c_\alpha$ of Lemma 2.2, any alphabet size $d\ge1$ and any best degree-$K$ approximant selected before the unknown law. Let $L=\log(ed)$, $C_\alpha=c_\alpha(256J)^{32J}$ and $\mathcal C=24C_\alpha^4/\min\{1,|1-\alpha|^2\}$. For every $0<\varepsilon\le1$, use two independent Poisson batches of positive mean $n$, where
--   $$n\ge\left\lceil\mathcal C^{1/(2\alpha)}\frac{d^{\max\{1,1/\alpha\}}}{\varepsilon^{1/\alpha}L}+\mathcal C\mathbf1_{\alpha>1/2}\frac{d^{|1-1/\alpha|}}{\varepsilon^2}\right\rceil.$$
--   For every $d$-letter probability law $p$, the exact clipped estimator (20)–(22) obeys
--   $$\Pr_p[|\widehat H-H_\alpha(p)|\le\varepsilon]\ge2/3.$$
--   The expected sample cost is $2n$. The budget attains the displayed sharp rate; arbitrary larger means are also valid by the same error bound. Singleton alphabets and zero coordinates are included.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: cα from Lemma 2.2 and Cα = cα(256J)^(32J) → any single c ≥ 1 satisfying both uniform bounds for every degree and every best approximant; C is computed from that c; reason: Lemma 2.2 asserts existence of this c; no error bound or success property is placed in the estimator definition
--   - reading: n = Θ(rate) without an explicit ε range → every 0 < ε ≤ 1 with the printed proof’s explicit ceiling; reason: the proof uses the logarithm estimate on relative error at most 1/2; this range includes the goal’s full small-accuracy regime
--   - encoding: the asymptotic upper budget in Theorem 4.1 → the exact constants and ceiling from printed page 17; reason: Ccal raised to 1/(2α) multiplies only the first term; constants depend solely on the fixed order and its single approximation constant
--   - generalization: take n to be the displayed ceiling → any positive real mean at least that ceiling; reason: Lemma 4.3 decreases in each budget term and gives the same success bound; the exact source choice is included
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 13,17 / PDF 15, 19, Theorem 4.1 and its explicit budget proof

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_Estimator

open MeasureTheory
open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Theorem 4.1, printed p.13 / PDF p.15, with the explicit budget in its
proof, printed p.17 / PDF p.19. The two batches have total expected cost 2n. -/
theorem noninteger_upper_bound (α c : ℝ) (hα : NonintegerOrder α)
    (hc : ApproximationConstant α c) (d : ℕ) (hd : 1 ≤ d)
    (Q : Polynomial ℝ) (hQ : IsBestApproximation α (approximationDegree d) Q)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℝ)
    (hn : 0 < n) (hbudget : (upperBudget α c d ε : ℝ) ≤ n) :
    ∀ p : Law d,
      (2 / 3 : ℝ≥0∞) ≤ (twoBatchLaw n p)
        {xy | |entropyEstimate α n d Q xy - entropy α p| ≤ ε} := by sorry

end WangRenyiEntropy.Noninteger
