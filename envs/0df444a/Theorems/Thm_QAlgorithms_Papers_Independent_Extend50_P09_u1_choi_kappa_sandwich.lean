-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_choi_kappa_sandwich
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_choi_kappa_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:38:56.415655+00:00
-- url     : https://prove2.me/theorems/61968c62-2580-4811-9daa-2430ae85b048
-- title:
--   Appendix B1: kappa bounds and large-n consequences
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   For the actual Choi $\Lambda$ of Appendix B1 define
--   $$\kappa=\sum_{i=0}^{n-t}\left(\sum_{j=0}^n
--   \frac{\binom{t}{j-i}\binom{k}{j-\alpha}}{\sqrt{2^k\binom{n}{j}}}\right)^2,$$
--   where binomials with negative or excessive lower indices are zero. Then
--   $$-\log_2\kappa\le H_{\min}(A^*|RE)_\Lambda\le-\log_2\frac{\kappa}{k+t+1}.$$
--
--   The two binomial coefficients in the numerator are not square-rooted. The physical outer range is clamped, and there are at most $k+t+1$ nonzero blocks.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 18, Appendix B1: kappa bounds and large-n consequences

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix B1, PDF p.18, (B24)–(B25), exact choiKappaValue sandwich.
The nonzero i-range has at most k+t+1 blocks, including boundary truncation. -/
theorem u1_choi_kappa_sandwich (n k t alpha : ℕ) (hk : k ≤ n) (ht : t ≤ n)
    (ha : alpha ≤ n-k) (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)))
    (hpsi : ChargeState alpha psi) :
    negLog (choiKappaValue n k t alpha) ≤ conditionalMinEntropy (choiLambda hk ht psi) ∧
    conditionalMinEntropy (choiLambda hk ht psi) ≤ negLog (choiKappaValue n k t alpha / (k+t+1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
