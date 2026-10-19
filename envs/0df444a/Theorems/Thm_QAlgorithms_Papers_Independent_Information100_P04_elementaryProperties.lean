-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_elementaryProperties
-- name    : QAlgorithms.Papers.Independent.Information100.P04.elementaryProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:28:41.407984+00:00
-- url     : https://prove2.me/theorems/366a91d5-1a12-47ba-b566-8bc681a63266
-- title:
--   Elementary properties and spectral lower bounds for both measurement functionals
-- statement:
--   Let $\rho$ be a density matrix on nonzero finite-dimensional systems $A:B$. Write $\Gamma$ for partial transpose on $B$, $L$ for the norm-score supremum in (9), and $\widetilde L$ for the absolute-operator score supremum in (35),(39). All logarithms and entropies are in bits.
--
--   1. Both functions are convex on density matrices, and
--   $$0\le L(\rho)\le\widetilde L(\rho)\le\log_2\|\rho^\Gamma\|_1.$$
--   They both vanish on PPT states.
--   2. For every density matrix $\omega_{AA':BB'}$, each function $H\in\{L,\widetilde L\}$ satisfies $H(\omega)\ge H(\omega_{A:B})+H(\omega_{A':B'})$.
--   3. For every PPT channel $\Lambda$, $L(\Lambda(\rho))\le L(\rho)$.
--   4. For an effect $0\le E\le I$, if $0\le E^\Gamma\le bI$ and $0<b<a=\operatorname{Tr}(\rho E)\le1$, then $\widetilde L(\rho)\ge\widetilde\ell(\rho,(E,I-E))\ge D_{\rm bin}(a\|b)$, where $D_{\rm bin}$ is binary relative entropy in bits.
--   5. Let $d=\min(d_A,d_B)$, let $-\nu_1,\ldots,-\nu_r$ be the strictly negative eigenvalues of $\rho^\Gamma$, and put $N=\sum_i\nu_i=(\|\rho^\Gamma\|_1-1)/2$, $s=(\sum_i\nu_i^2)^{1/2}$, and $q=\sqrt{(d-1)/(2d)}$. If $d\ge2$, then
--   $$\widetilde L(\rho)\ge\max\left\{D_{\rm bin}\!\left(\frac{1+s}{1+q}\middle\|\frac1{1+q}\right),\ D_{\rm bin}\!\left(\frac{d+1+2N}{2d}\middle\|\frac{d+1}{2d}\right)\right\}.$$
--   If also $N>0$, set $k=\min\{\sqrt r,(d+1)/2\}$. Then $\widetilde L(\rho)\ge1-h_2(1/2+N/(2k))\ge1-h_2(1/2+N/(d+1))$. Both displayed divergence terms vanish at $N=0$. If $d=1$, the state is separable and $\widetilde L(\rho)=0$.
--
--   These properties supply achievable spectral bounds. Single-copy monotonicity under PPT channels is asserted only for $L$.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 12, Proposition8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 8, PDF pp.12–15: all five elementary-property clauses.
There is no assertion of single-copy PPT monotonicity for L-tilde. -/
theorem elementaryProperties {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    (0 ≤ L rho ∧ L rho ≤ LTilde rho ∧ LTilde rho ≤ Real.logb 2 (traceNorm (gamma rho))) ∧
    (Entanglement.negativity rho = ∑ k, -min (ascEigenvalues (gamma rho) k) 0) ∧
    (IsPPT rho → L rho = 0 ∧ LTilde rho = 0) ∧
    (∀ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        L ((t:ℂ) • rho + ((1-t:ℝ):ℂ) • sigma) ≤ t*L rho+(1-t)*L sigma ∧
        LTilde ((t:ℂ) • rho + ((1-t:ℝ):ℂ) • sigma) ≤ t*LTilde rho+(1-t)*LTilde sigma) ∧
    (∀ (C D : Type) [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
      [Nonempty C] [Nonempty D]
      (omega : Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ),
      IsDensityMatrix omega →
        L (principalMarginal omega) + L (ancillaryMarginal omega) ≤ L omega ∧
        LTilde (principalMarginal omega) + LTilde (ancillaryMarginal omega) ≤ LTilde omega) ∧
    (∀ (C D : Type) [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
      [Nonempty C] [Nonempty D] (Phi : Superop (A × B) (C × D)),
      IsPPTChannel Phi → L (Phi rho) ≤ L rho) ∧
    (∀ (E : Matrix (A × B) (A × B) ℂ) (b : ℝ), IsEffect E →
      (gamma E).PosSemidef → ((b:ℂ) • 1 - gamma E).PosSemidef →
      0 < b → b < effectProb E rho → effectProb E rho ≤ 1 →
      binaryD (effectProb E rho) b ≤ ellTilde rho (![E,1-E]) ∧
        ellTilde rho (![E,1-E]) ≤ LTilde rho) ∧
    (let d : ℝ := min (Fintype.card A) (Fintype.card B)
     let N := Entanglement.negativity rho
     let s := negativeLength rho
     let q := Real.sqrt ((d-1)/(2*d))
     let k := min (Real.sqrt (negativeRank rho)) ((d+1)/2)
     (2 ≤ d →
       max (binaryD ((1+s)/(1+q)) (1/(1+q)))
         (binaryD ((d+1+2*N)/(2*d)) ((d+1)/(2*d))) ≤ LTilde rho) ∧
     (2 ≤ d → 0 < N →
       1-binEntropy2 (1/2+N/(d+1)) ≤ 1-binEntropy2 (1/2+N/(2*k)) ∧
       1-binEntropy2 (1/2+N/(2*k)) ≤ LTilde rho) ∧
     (2 ≤ d → N = 0 →
       binaryD ((1+s)/(1+q)) (1/(1+q)) = 0 ∧
       binaryD ((d+1+2*N)/(2*d)) ((d+1)/(2*d)) = 0) ∧
     (d = 1 → Entanglement.IsSeparableDensity rho ∧ LTilde rho = 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
