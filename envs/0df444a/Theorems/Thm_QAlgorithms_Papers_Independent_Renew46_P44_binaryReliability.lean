-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_binaryReliability
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.binaryReliability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:30:23.524953+00:00
-- url     : https://prove2.me/theorems/af271062-15cf-4892-84e0-bb7d53da17a2
-- title:
--   §III.3: binary spectra, optimizing prior and reliability regions
-- statement:
--   Let two unit pure signals in a two-dimensional complex Hilbert space have overlap magnitude $0<\epsilon<1$. For the prior $\Pr(1)=p\in[0,1]$, the two possibly nonzero mean-state eigenvalues are
--
--   $$\lambda_\pm(p)=\frac{1\pm\sqrt{1-4(1-\epsilon^2)p(1-p)}}2.$$
--
--   The random scalar $-\log(\lambda_-^{1+s}+\lambda_+^{1+s})$ for $0\le s\le1$ and the expurgated scalar $-s\log[p^2+(1-p)^2+2p(1-p)\epsilon^{2/s}]$ for $s\ge1$ are maximized by $p=1/2$. Write
--
--   $$\mu(s)=-\log\left[\left(\frac{1-\epsilon}2\right)^{1+s}+\left(\frac{1+\epsilon}2\right)^{1+s}\right],\quad
--   \widetilde\mu(s)=-s\log\frac{1+\epsilon^{2/s}}2,$$
--
--   $$c=\mu(1)=\widetilde\mu(1)=-\log\frac{1+\epsilon^2}2,\quad
--    a=\widetilde\mu'(1)=c+\frac{\epsilon^2\log\epsilon^2}{1+\epsilon^2},$$
--
--   $$b=\mu'(1)=-\frac{(1-\epsilon)^2\log((1-\epsilon)/2)+(1+\epsilon)^2\log((1+\epsilon)/2)}{2(1+\epsilon^2)},\quad
--    C=\mu'(0)=-\sum_{\pm}\frac{1\pm\epsilon}2\log\frac{1\pm\epsilon}2.$$
--
--   For $0<R<C$, the average-error reliability function obeys
--
--   $$E(R)\ge\begin{cases}\widetilde\mu(t)-tR,&R\le a,\quad t\ge1,\ \widetilde\mu'(t)=R,\\
--   c-R,&a\le R\le b,\\
--   \mu(s)-sR,&b\le R,\quad 0\le s\le1,\ \mu'(s)=R.
--   \end{cases}$$
--
--   The roots exist in the indicated intervals and shared endpoints are retained. This describes achievable bounds, not the exact reliability function.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 14, §III.3: binary spectra, optimizing prior and reliability regions

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14-15: binary spectra, uniform-prior optimization, derivatives,
and all three reliability lower-bound regions with their shared endpoints.
Root formulas are restricted to 0<epsilon<1. -/
theorem binaryReliability (psi : Bool → Hilbert (Fin 2))
    (hpsi : ∀ b, ‖psi b‖ = 1) (epsilon : ℝ)
    (hoverlap : ‖inner ℂ (psi false) (psi true)‖ = epsilon)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      compactApproximationValue (discretePureMean psi (bernoulliInputLaw p hp0 hp1)) 0 = binaryLambdaHigh epsilon p ∧
      compactApproximationValue (discretePureMean psi (bernoulliInputLaw p hp0 hp1)) 1 = binaryLambdaLow epsilon p ∧
      (∀ j : ℕ, 2 ≤ j → compactApproximationValue (discretePureMean psi (bernoulliInputLaw p hp0 hp1)) j = 0) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        pureMu psi (bernoulliInputLaw p hp0 hp1) s =
          -Real.log ((binaryLambdaLow epsilon p) ^ (1 + s) +
            (binaryLambdaHigh epsilon p) ^ (1 + s)) ∧
        pureMu psi (bernoulliInputLaw p hp0 hp1) s ≤ binaryMu epsilon s) ∧
      (∀ s : ℝ, 1 ≤ s →
        pureExpurgatedMu psi (bernoulliInputLaw p hp0 hp1) s =
          -s * Real.log (p ^ 2 + (1 - p) ^ 2 + 2 * p * (1 - p) * epsilon ^ (2 / s)) ∧
        pureExpurgatedMu psi (bernoulliInputLaw p hp0 hp1) s ≤ binaryExpurgatedMu epsilon s)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      pureMu psi (bernoulliInputLaw (1 / 2) (by norm_num) (by norm_num)) s = binaryMu epsilon s) ∧
    (∀ s : ℝ, 1 ≤ s →
      pureExpurgatedMu psi (bernoulliInputLaw (1 / 2) (by norm_num) (by norm_num)) s =
        binaryExpurgatedMu epsilon s) ∧
    binaryMu epsilon 1 = -Real.log ((1 + epsilon ^ 2) / 2) ∧
    binaryExpurgatedMu epsilon 1 = binaryMu epsilon 1 ∧
    deriv (binaryExpurgatedMu epsilon) 1 =
      binaryMu epsilon 1 + epsilon ^ 2 * Real.log (epsilon ^ 2) / (1 + epsilon ^ 2) ∧
    deriv (binaryMu epsilon) 1 =
      -((1 - epsilon) ^ 2 * Real.log ((1 - epsilon) / 2) +
        (1 + epsilon) ^ 2 * Real.log ((1 + epsilon) / 2)) / (2 * (1 + epsilon ^ 2)) ∧
    deriv (binaryMu epsilon) 0 = binaryCapacityValue epsilon ∧
    averageErrorCqCapacity (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 =
      ENNReal.ofReal (binaryCapacityValue epsilon) ∧
    (∀ R : ℝ, 0 < R → R < binaryCapacityValue epsilon →
      (R ≤ deriv (binaryExpurgatedMu epsilon) 1 →
        ∃ t : ℝ, 1 ≤ t ∧ HasDerivAt (binaryExpurgatedMu epsilon) R t ∧
          ENNReal.ofReal (binaryExpurgatedMu epsilon t - t * R) ≤
            reliability (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 R) ∧
      (deriv (binaryExpurgatedMu epsilon) 1 ≤ R → R ≤ deriv (binaryMu epsilon) 1 →
        ENNReal.ofReal (binaryMu epsilon 1 - R) ≤
          reliability (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 R) ∧
      (deriv (binaryMu epsilon) 1 ≤ R →
        ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ HasDerivAt (binaryMu epsilon) R s ∧
          ENNReal.ofReal (binaryMu epsilon s - s * R) ≤
            reliability (fun b => TC.rankOne (psi b)) (fun _ => 0) 0 R)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
