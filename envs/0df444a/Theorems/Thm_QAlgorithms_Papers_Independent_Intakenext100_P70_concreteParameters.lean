-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_concreteParameters
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.concreteParameters
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:45:24.790396+00:00
-- url     : https://prove2.me/theorems/100c7dca-e616-4387-8500-240fd60a45e1
-- title:
--   Concrete growing-dimension witnesses
-- statement:
--   Let $n\geq1$ and $m\geq68$ be integers, and set
--   $$
--   \kappa=\frac14,\quad p=(1+4^{-n})^{-1/n},\quad N=2n4^n,\quad
--   q=\frac13,\quad r=2m+\lceil\log_2m\rceil,\quad d=2Nr.
--   $$
--   Construct $\Gamma$ from the normalized Choi state (S18) and $\mathcal M$ from (S15). The parameters are admissible and satisfy (S19), $\Gamma$ is PPT-binding, and $\mathcal M$ is completely positive and trace preserving. Moreover $N+1>n$, $p^N<1/3$, and
--   $$
--   Q^{(n)}(\mathcal M)=0,\qquad Q^{(N+1)}(\mathcal M)>0,\qquad Q(\mathcal M)>0.
--   $$
--   More precisely, there is a perfect private bit $\gamma$ on the first-share registers for which, writing $\rho$ for the computed marginal (S20), $\tau=\|\rho-\gamma\|_1$ and $\Delta=4\tau+2h_2(\tau)$, one has $0\leq\tau<1$, $\tau\leq16\sqrt m\,2^{-m/4}$ and
--   $$
--   \Delta\leq72\,2^{-m/4}m^{3/2}<\frac13,\qquad
--   (N+1)Q^{(N+1)}(\mathcal M)\geq\frac34(1-p^N-\Delta)-\frac14.
--   $$
--   Here $h_2$ is binary entropy in bits and $\|\cdot\|_1$ is the full trace norm. The scalar bounds are consequences of the specified choices, not additional assumptions.
--
--   These parameters make the arbitrary-block-length phenomenon concrete. The source's intermediate logarithmic sufficiency inference is corrected; the final values of $N$ and $m$ are preserved.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 11, Unnumbered parameter choice following the Supplementary Theorem; S46–S54, p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Unnumbered concrete parameter choice, PDF p.11, using S46--S54 on p.10.
SOURCE CORRECTION: the paragraph's upper bound on log(1+x) alone does not justify a
sufficient N. The final N=2*n*4^n is retained: log(1+x)>=x/(1+x) verifies it.
The ceiling in r is retained from Lemma 2. The raw bound below retains the factor N+1. -/
theorem concreteParameters (n m : ℕ) (hn : 0 < n) (hm : 68 ≤ m) :
    let P := cubittExplicitParameters n m
    let p := cubittErasureThreshold n (1 / 4)
    CubittValid P ∧ CubittPPTCondition P ∧ CubittPPTBinding (cubittGammaChannel P) ∧
    IsChannel (cubittPaperChannel P (1 / 4) p) ∧
    n < P.N + 1 ∧ p ^ P.N < (1 / 3 : ℝ) ∧
    cubittBlockInformation (cubittPaperChannel P (1 / 4) p) n = 0 ∧
    0 < cubittBlockInformation (cubittPaperChannel P (1 / 4) p) (P.N + 1) ∧
    0 < quantumCapacity (cubittPaperChannel P (1 / 4) p) ∧
    ∃ hN : 0 < P.N,
    ∃ rho : Op ((Bool × CubittShare P.r P.m P.d) × (Bool × CubittShare P.r P.m P.d)),
      CubittPerfectPbit rho ∧
      let tau := traceNorm (cubittFirstShareState P hN - rho)
      0 ≤ tau ∧ tau < 1 ∧ tau ≤ cubittApproximationBound m ∧
      cubittContinuityLoss tau ≤ 72 * (2 : ℝ) ^ (-(m : ℝ) / 4) * (m : ℝ) ^ ((3 : ℝ) / 2) ∧
      cubittContinuityLoss tau < 1 / 3 ∧
      (1 - (1 / 4 : ℝ)) * (1 - p ^ P.N - cubittContinuityLoss tau) - 1 / 4 ≤
        ((P.N + 1 : ℕ) : ℝ) * cubittBlockInformation (cubittPaperChannel P (1 / 4) p) (P.N + 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
