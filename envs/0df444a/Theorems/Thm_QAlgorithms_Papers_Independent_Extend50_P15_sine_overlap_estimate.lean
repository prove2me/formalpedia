-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_sine_overlap_estimate
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.sine_overlap_estimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:59:57.656994+00:00
-- url     : https://prove2.me/theorems/93604735-1d59-4827-b983-07963193f2be
-- title:
--   Uniform bounded-shift estimate for the raw sine coefficients
-- statement:
--   Fix an integer cutoff $n_0\ge0$. For integer $k$ define the raw coefficients
--
--   $$g_k^{(M)}=\frac2{M+1}\sin^2\!\left(\frac{\pi(2k+1)}{2(M+1)}\right).$$
--
--   There are constants $C>0$ and $M_0\ge\max\{1,4n_0+1\}$, chosen before $M$ and the shift, such that for all integers $M\ge M_0$ and $\delta\in\mathbb Z$ with $|\delta|\le n_0$,
--
--   $$1-\sum_{k=2n_0}^{M-2n_0}\sqrt{g_k^{(M)}g_{k+\delta}^{(M)}}\le\frac12\left(\frac{\pi\delta}{M+1}\right)^2+\frac C{M^3}.$$
--
--   This is the source's bounded-shift $O(M^{-3})$ remainder with explicit quantifier order. It estimates raw coefficients and supplies no normalization or valid Young-diagram grid for Theorem 1.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 22, B8,B10; calculation B.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- B10 and B.4, PDF pp.22--24: a uniform remainder for the bounded shifts used in
Sdiff. Constants and threshold are chosen before M and delta. The theorem concerns raw
coefficients and does not repair or assume the invalid reference state of Theorem 1. -/
theorem sine_overlap_estimate (n0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ M0 : ℕ, max 1 (4 * n0 + 1) ≤ M0 ∧
      ∀ M : ℕ, M0 ≤ M → ∀ delta : ℤ, |delta| ≤ (n0 : ℤ) →
        sineOverlapError n0 M delta ≤
          (1 / 2 : ℝ) * (Real.pi * (delta : ℝ) / ((M : ℝ) + 1)) ^ 2 +
            C / (M : ℝ) ^ 3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
