-- Prove2me | Theorems.Thm_UnknownCovDP_General_lemma_A_1
-- name    : UnknownCovDP.General.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:16.51705+00:00
-- url     : https://prove2.me/theorems/8bab6756-cfd3-4921-a533-50fc03252cbc
-- title:
--   Lemma A.1 — concentration of the empirical covariance
-- statement:
--   There is a numerical constant $c>0$ such that the following holds for all $d,k$ and $n\ge1$. Let $\Sigma$ be a rank-$k$ orthogonal projection in $\mathbb R^d$ and $X\sim N(0,\Sigma)^{\otimes n}$. If $n\le ck$, then
--   $$\frac{k}{2n}P_X\preceq\hat\Sigma_X\preceq\frac{2k}{n}P_X$$
--   with probability at least $1-2\exp(-ck)$.
--
--   Here $P_X$ is the orthogonal projection onto the span of the sample and $\hat\Sigma_X=\frac1n XX^\top$. On its span, the empirical covariance is a multiple of the identity up to constant factors.
--
--   **Formalization Note** A rank-$k$ orthogonal projection is a symmetric idempotent matrix of rank $k$.
--
--   Differences from the source:
--   - reading: "There is a numerical constant c > 0" after Σ and X are introduced → ∃ c before ∀ d k n S; reason: numerical means independent of d, k, n, Σ; this is the stronger reading
--   - encoding: n is a sample size, with division by n in the empirical covariance and test averages → hypothesis 1 ≤ n; reason: these sample averages are defined for positive sample size; the source does not use c/n in this result
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Lemma A.1, printed p. 31 (PDF p. 32)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Lemma A.1 (Concentration of the empirical covariance), printed p. 31, PDF p. 32. With a numerical
constant `c > 0`: if `S` is a rank-`k` orthogonal projection in `ℝ^d`, `X ∼ N(0,S)^{⊗n}` and `n ≤ ck`,
then `(k/2n) P_X ⪯ Σ̂_X ⪯ (2k/n) P_X` with probability at least `1 − 2 exp(−ck)`. -/
theorem lemma_A_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d k n : ℕ) (S : Mat d), S.IsHermitian → S * S = S → S.rank = k →
      1 ≤ n → (n : ℝ) ≤ c * k →
      ENNReal.ofReal (1 - 2 * Real.exp (-(c * k))) ≤
        dataLaw n (0 : Vec d) S {X | EventG1 k X} := by sorry

end UnknownCovDP.General
