-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_choi_lambda_exact
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_choi_lambda_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:37:27.819354+00:00
-- url     : https://prove2.me/theorems/45b7af3e-8ffa-4875-99ca-acf37f3f5802
-- title:
--   Appendix B1: exact Choi Lambda and SDP reduction
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   Let $A=A_1A_2$, where $A_1$ has $k$ qubits, and let $\Psi=\Phi_k^{RA_1}\otimes\psi_\alpha^{A_2}$. For a physical charge $j\in[\alpha,\alpha+k]$, let $\phi_q^{(m)}$ be the normalized maximally entangled vector on the weight-$q$ sector of two $m$-qubit registers. Then
--   $$\Pi_j^A|\Psi\rangle=\sqrt{\binom{k}{j-\alpha}/2^k}\,|\phi_{j-\alpha}^{(k)}\rangle|\psi_\alpha\rangle,$$
--   $$\Lambda=\sum_{i=0}^{n-t}\Pi_i^{(n-t)}\otimes|\Gamma_i\rangle\langle\Gamma_i|,\qquad H_{\min}(\Lambda)=-\log_2 s(\Lambda).$$
--   Here $s(X)=\inf\{\operatorname{Tr}\sigma:\sigma\ge0,\ I\otimes\sigma\ge X\}$, and
--   $$|\Gamma_i\rangle=\sum_{\substack{0\le j\le n\\0\le j-i\le t\\0\le j-\alpha\le k}}
--   \sqrt{\frac{\binom{t}{j-i}\binom{k}{j-\alpha}}{2^k\binom{n}{j}}}
--   |\phi_{j-i}^{(t)}\rangle|\phi_{j-\alpha}^{(k)}\rangle|\psi_\alpha\rangle.$$
--
--   These are identities for the independently constructed $\Lambda$; the $\Gamma_i$ need not have unit norm.
--
--   For every physical block $0\le i\le n-t$, let $G_i=|\Gamma_i\rangle\langle\Gamma_i|$ on the bipartition $(\bar A_1A_1A_2):(RE)$. Its individual SDP value and entropy are
--   $$s(G_i)=s_i,\qquad H_{\min}(G_i)=-\log_2s_i,\qquad s_i=\left(\sum_{j=0}^n\frac{\binom t{j-i}\binom k{j-\alpha}}{\sqrt{2^k\binom nj}}\right)^2.$$
--   This retains (B22)–(B23), with $s_i=0$ and entropy $+\infty$ for a zero block.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 17, Appendix B1: exact Choi Lambda and SDP reduction

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

/-- Appendix B1, PDF p.17, (B7),(B10)–(B14): exact physical Lambda
factorization and the SDP reduction, with the individual Gamma_i SDP and
entropy values (B22)–(B23). i runs only through 0,...,n-t; zero Gamma_i have
SDP value zero and extended entropy +infinity. -/
theorem u1_choi_lambda_exact (n k t alpha : ℕ) (hk : k ≤ n) (ht : t ≤ n)
    (ha : alpha ≤ n-k) (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)))
    (hpsi : ChargeState alpha psi) :
    (∀ j : ℕ, alpha ≤ j → j ≤ alpha+k → ∀ r : CovariantWord 2 k, ∀ a : CovariantWord 2 n,
      (if chargeHammingWeight a = j then initialChoi hk psi (r,a) else 0) =
        (Real.sqrt ((k.choose (j-alpha) : ℝ)/(2 : ℝ)^k) : ℂ) *
          sectorBell k (j-alpha) (firstCoordinates hk a,r) * psi (remainingCoordinates a)) ∧
    (∀ a b : (CovariantWord 2 n × CovariantWord 2 n) × (CovariantWord 2 k × CovariantWord 2 t),
      choiLambda hk ht psi a b =
        ∑ i ∈ Finset.range (n-t+1),
          u1SectorProjector (n-t) i (remainingCoordinates (k := t) a.1.2) (remainingCoordinates (k := t) b.1.2) *
          choiGammaCoefficient hk ht alpha psi i a.1.1 (firstCoordinates ht a.1.2) a.2.1 a.2.2 *
          conj (choiGammaCoefficient hk ht alpha psi i b.1.1 (firstCoordinates ht b.1.2) b.2.1 b.2.2)) ∧
    (∀ i : ℕ, i ≤ n-t →
      let G : Op ((CovariantWord 2 n × CovariantWord 2 t) ×
          (CovariantWord 2 k × CovariantWord 2 t)) := fun a b =>
        choiGammaCoefficient hk ht alpha psi i a.1.1 a.1.2 a.2.1 a.2.2 *
        conj (choiGammaCoefficient hk ht alpha psi i b.1.1 b.1.2 b.2.1 b.2.2)
      let si := (∑ j ∈ Finset.range (n+1),
        chooseZ t ((j : ℤ)-i) * chooseZ k ((j : ℤ)-alpha) /
          Real.sqrt ((2 : ℝ)^k * (n.choose j : ℝ)))^2
      sdp G = si ∧ conditionalMinEntropy G = negLog si) ∧
    conditionalMinEntropy (choiLambda hk ht psi) = negLog (sdp (choiLambda hk ht psi)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
