-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_recovering_fixed_size_spectrum
-- name    : SingleCopyMoments.Adaptive.Supplement.recovering_fixed_size_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:42:41.940039+00:00
-- url     : https://prove2.me/theorems/5dd2a85b-f547-4e83-864d-57d144e903fd
-- title:
--   Lemma 9 — Recovering a fixed-size spectrum
-- statement:
--   Fix $r\ge2$ and $\epsilon>0$. Let $\Delta_r^\downarrow$ denote all nonincreasing nonnegative real vectors of length $r$ summing to one. There is $\delta>0$, chosen before the two vectors and depending only on $r,\epsilon$, such that
--   $$\lambda,\mu\in\Delta_r^\downarrow,\quad
--    \max_{2\le j\le r}|p_j(\lambda)-p_j(\mu)|<\delta
--    \ \Longrightarrow\ \sum_{i=1}^r|\lambda_i-\mu_i|<\epsilon,
--   \qquad p_j(\lambda)=\sum_i\lambda_i^j.$$
--   Both the antecedent and the conclusion are strict. Zero and repeated coordinates are included, without a spectral-gap condition.
--
--   This uniform inverse-continuity result supports Theorem 28, translating moment accuracy into error of the entire sorted spectrum.
--
--   Differences from the source:
--   - encoding: strict maximum bound over 2<=j<=r → the strict bound holds for each j in Finset.Icc 2 r; reason: the index set is finite and nonempty for r>=2, so the antecedents are equivalent
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 9, printed p. 14 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Spectra

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Lemma 9, printed p.14 / PDF p.16; strict antecedent and conclusion. -/
theorem recovering_fixed_size_spectrum (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ lam mu : SortedProbVec r,
      (∀ j ∈ Finset.Icc 2 r, |powerSumVector lam j - powerSumVector mu j| < δ) →
      l1Distance lam.val mu.val < ε := by sorry

end SingleCopyMoments.Adaptive.Supplement
