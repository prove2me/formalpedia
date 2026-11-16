-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_hypertree_privacy
-- name    : PrivateContinualCounting.Kraft.Supplement.hypertree_privacy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:27.809551+00:00
-- url     : https://prove2.me/theorems/d8fbe59d-714e-45da-8cd5-13e90d540718
-- title:
--   Lemma 5.2 — actual hypertree factorization and unit GDP
-- statement:
--   Fix $a>0$ and $0<\xi<1$, and form the A/B/C factors and releases of Section 5 using the square-root inner family. There exists an actual Gaussian factorization counter on their one countable product seed whose decoder, strategy and noise process are precisely those formulas, and
--   $$LR=A,\qquad\Delta^2=1,\qquad (Y_1,\ldots,Y_n)\text{ is }1\text{-GDP for every }n\ge1.$$
--   The counter's transcript law is identified with the directly defined Section 5 release law for every stream and horizon. Exact factorization and row/column summability are part of constructing the published Gaussian-counter object; sensitivity equality and testing privacy are additional conclusions. No privacy or desired covariance is assumed in the raw hypertree data. This establishes privacy for the single infinite causal mechanism.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: factor sensitivity Delta=1 → squared sensitivity deltaSq=1; reason: factor sensitivity is nonnegative, so these equalities are equivalent
--   - encoding: the constructed infinite Gaussian factorization counter → existence of a counter with exactly the computed matrices and finite-row Gaussian sums, plus equality of transcript laws; reason: no product, sensitivity or privacy property is assumed of the raw construction
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 11, PDF p. 13, Lemma 5.2

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Hypertree

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 5.2: exact factorization, exact sensitivity and actual transcript GDP. -/
theorem hypertree_privacy (a ξ : ℝ) (ha : 0 < a) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ∃ M : GaussianCounter TreeIndex,
      IsTree M squareRootFamily a ξ ∧ M.factors.deltaSq = 1 ∧
      TranscriptGDP (treeLaw squareRootFamily a ξ) 1 ∧
      (∀ x : Stream, ∀ n : ℕ,
        M.transcriptLaw ⟨1, by norm_num⟩ x n = treeLaw squareRootFamily a ξ x n) := by sorry

end PrivateContinualCounting.Kraft.Supplement
