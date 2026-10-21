-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_unique_optimal_cloner
-- name    : QAlgorithms.Papers.Independent.Support21.P16.unique_optimal_cloner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:36:38.115919+00:00
-- url     : https://prove2.me/theorems/f8f176ff-908f-437c-931c-baef6ec72b29
-- title:
--   The unique optimal pure-state cloner
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers, and identify the one-particle Hilbert space with $H=\mathbb C^d$. Let $s_k$ project onto the permutation-fixed Bose subspace of $H^{\otimes k}$, and write $D_k=\binom{d+k-1}{k}$. An admissible cloner $T$ is a complex-linear completely positive trace-preserving map from the $N$-particle Bose operator algebra to the full $M$-particle operator algebra. Maps are extended to ambient inputs by $T(A)=T(s_NAs_N)$. Define
--   $$
--   \mathcal F(T)=\inf_{\|\phi\|=1}\operatorname{Re}\operatorname{tr}\!\left[|\phi^{\otimes M}\rangle\langle\phi^{\otimes M}|\,T(|\phi^{\otimes N}\rangle\langle\phi^{\otimes N}|)\right].
--   $$
--   The concrete map $\widehat T(A)=(D_N/D_M)s_M((s_NAs_N)\otimes I^{\otimes(M-N)})s_M$ is admissible, and every admissible $T$ satisfies
--   $$
--   \mathcal F(T)\le\frac{D_N}{D_M},\qquad
--   \mathcal F(T)=\frac{D_N}{D_M}\ \Longleftrightarrow\ T=\widehat T.
--   $$
--   This gives both the sharp many-particle overlap and full uniqueness on the effective input algebra. No covariance or symmetric-output hypothesis restricts competitors; $d=1$ is retained.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 9, §4, unnumbered Theorem: unique optimal pure-state cloner

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF pp.9–10, unnumbered Theorem (abstract p.1): SHARP global bound and
FULL iff uniqueness among all corner-input CP TP maps with full tensor output.
Covariance and symmetric output are conclusions for the optimizer, never
hypotheses on competitors. In particular the statement retains d=1. -/
theorem unique_optimal_cloner (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    IsBoseInputChannel (canonicalCloner (d := d) hNM.le) ∧
    ∀ T : CloneMap d N M, IsBoseInputChannel T →
      cloningFidelity T ≤ (boseDimension d N : ℝ) / boseDimension d M ∧
      (cloningFidelity T = (boseDimension d N : ℝ) / boseDimension d M ↔
        T = canonicalCloner hNM.le) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
