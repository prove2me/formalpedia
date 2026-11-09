-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_relative_mse
-- name    : WangRenyiEntropy.Noninteger.relative_mse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:45.705611+00:00
-- url     : https://prove2.me/theorems/ea44d83c-abfb-4d2f-b09f-52a2b151ed06
-- title:
--   Lemma 4.3 — relative mean square error of the power-sum estimate
-- statement:
--   Fix any positive noninteger $\alpha$, a uniform approximation constant $c_\alpha$ of Lemma 2.2, any $d\ge1$, a best degree-$K$ approximant, any mean $n>0$, and any $d$-letter law $p$. Use the two independent count batches in (20) and write $C_\alpha=c_\alpha(256J)^{32J}$. The squared relative error is integrable and satisfies
--   $$\mathbb E\left[\left(\frac{\widehat F-F_\alpha(p)}{F_\alpha(p)}\right)^2\right]\le C_\alpha^4\left(\frac{d^{\max\{2,2\alpha\}}}{(nL)^{2\alpha}}+\mathbf1_{\alpha>1/2}\frac{d^{|1-1/\alpha|}}n\right).$$
--   Here $\widehat F$ is the unclipped estimator and $F_\alpha(p)>0$. The result holds for every nonempty finite alphabet and every positive Poisson mean, without an accuracy or asymptotic-size restriction.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: cα from Lemma 2.2 and Cα = cα(256J)^(32J) → any single c ≥ 1 satisfying both uniform bounds for every degree and every best approximant; C is computed from that c; reason: Lemma 2.2 asserts existence of this c; no error bound or success property is placed in the estimator definition
--   - encoding: expected squared relative error → integrability of that square is explicit in the conclusion; reason: excludes use of a default real integral; all Poisson moments required by the estimator are finite
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 16 / PDF 18, Lemma 4.3, Eq. (38)

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_Estimator

open MeasureTheory

namespace WangRenyiEntropy.Noninteger

/-- Lemma 4.3, printed p.16 / PDF p.18: the actual unclipped estimator.
No large-alphabet or accuracy restriction. -/
theorem relative_mse (α c : ℝ) (hα : NonintegerOrder α)
    (hc : ApproximationConstant α c) (d : ℕ) (hd : 1 ≤ d)
    (Q : Polynomial ℝ) (hQ : IsBestApproximation α (approximationDegree d) Q)
    (n : ℝ) (hn : 0 < n) (p : Law d) :
    let μ := twoBatchLaw n p
    let R := fun xy => ((powerEstimate α n d Q xy - powerSum α p) / powerSum α p) ^ 2
    Integrable R μ ∧
    (∫ xy, R xy ∂μ) ≤ (estimatorConstant α c) ^ 4 *
      (Real.rpow d (max 2 (2 * α)) / Real.rpow (n * logScale d) (2 * α) +
        if 1 / 2 < α then Real.rpow d |1 - 1 / α| / n else 0) := by sorry

end WangRenyiEntropy.Noninteger
