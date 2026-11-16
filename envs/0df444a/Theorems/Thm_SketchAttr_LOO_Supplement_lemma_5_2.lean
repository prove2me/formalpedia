-- Prove2me | Theorems.Thm_SketchAttr_LOO_Supplement_lemma_5_2
-- name    : SketchAttr.LOO.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:53:20.401033+00:00
-- url     : https://prove2.me/theorems/317f9680-60f1-4d12-bb01-0044018e5d2d
-- title:
--   Lemma 5.2 — PSD diagonal-estimation lower bound
-- statement:
--   There are universal constants $b,c>0$, with $c\le1$, such that the following holds for every $n\ge1$. Fix any randomized adaptive real matrix-vector procedure with worst-case budget $q$. If, for every real positive semidefinite $n\times n$ matrix $A$ with $\|A\|_F\le1/16$, it satisfies
--
--   $$\Pr_{\mathrm{seed}}\!\left(\sum_{i=1}^n|\widehat L_i-A_{ii}|^2\le c^2/n\right)\ge\frac23,$$
--
--   then
--
--   $$q>bn.$$
--
--   This is the explicit universal-constant meaning of the paper's $\Omega(n)$ query requirement. It supports the reduction from attribution to diagonal estimation. The seed law and all query and output maps are fixed before the unknown matrix.
--
--   Differences from the source:
--   - encoding: indices in [n] and probabilities over random seeds → indices in Fin n and an arbitrary measurable seed probability space; reason: zero-based labels and explicit probability laws change no instance
--   - encoding: there is c greater than zero and a query lower bound Omega(n) → there are universal b and c greater than zero with c at most one and q greater than bn; reason: this exposes the stopping-after-budget form proved in Appendix C; c can be decreased to at most one
--   - encoding: a randomized adaptive procedure with a worst-case query budget → a measurable fixed-length transcript padded for any earlier stopping; reason: the same oracle access and success guarantee are retained without a computation restriction
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, p. 19, Lemma 5.2; repeated pp. 28–29 and proved p. 29

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Quadratic

open MeasureTheory
open scoped ENNReal

namespace SketchAttr.LOO.Supplement

theorem lemma_5_2 :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (Seed : Type) [MeasurableSpace Seed]
        (μ : Measure Seed) [IsProbabilityMeasure μ] (q : ℕ)
        (P : MatrixProcedure Seed n q),
      (∀ A : RealMatrix n, A.PosSemidef → matrixFrobNorm A ≤ 1/16 →
        (2/3 : ℝ≥0∞) ≤ μ {seed | squaredDiagonalError (matrixEstimate P A seed) A ≤
          c^2 / n}) →
      b * n < (q : ℝ) := by sorry

end SketchAttr.LOO.Supplement
