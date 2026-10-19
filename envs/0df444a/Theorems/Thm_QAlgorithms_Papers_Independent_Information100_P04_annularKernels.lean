-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_annularKernels
-- name    : QAlgorithms.Papers.Independent.Information100.P04.annularKernels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:36:50.101978+00:00
-- url     : https://prove2.me/theorems/ea4d39ba-2f71-4f4f-8c34-7855e0ca594d
-- title:
--   Periodized strip weights equal the annular Fourier kernels
-- statement:
--   Let $0<a<r<b$ and $\varphi\in\mathbb R$, set $\ell=\ln(b/a)$, $\theta=\ln(r/a)/\ell\in(0,1)$, and $\beta_\theta(s)=\sin(\pi\theta)/[2\theta(\cosh(\pi s)+\cos(\pi\theta))]$. Define $h_0=(1-\theta)\beta_{1-\theta}$ and $h_1=\theta\beta_\theta$. These are integrable nonnegative even functions of masses $1-\theta$ and $\theta$. For $u>0$, their cosine transforms are $\sinh((1-\theta)u)/\sinh u$ and $\sinh(\theta u)/\sinh u$, respectively. Define $k_j(\psi)=(2\pi/\ell)\sum_{m\in\mathbb Z}h_j((\psi-\varphi+2\pi m)/\ell)$. The series are summable pointwise and their symmetric partial sums converge uniformly on one full period. The resulting nonnegative periodic kernels have the exact Fourier forms
--
--   $$k_0(\psi)=1-\theta+2\sum_{n\ge1}\frac{(a/r)^n[1-(r/b)^{2n}]}{1-(a/b)^{2n}}\cos(n(\psi-\varphi)),\qquad k_1(\psi)=\theta+2\sum_{n\ge1}\frac{(r/b)^n[1-(a/r)^{2n}]}{1-(a/b)^{2n}}\cos(n(\psi-\varphi)).$$
--
--   Their masses relative to $d\psi/(2\pi)$ are $1-\theta$ and $\theta$. For any two continuous $2\pi$-periodic real boundary functions $f_0,f_1$, the strip integrand is integrable and its integral equals $(2\pi)^{-1}\int_0^{2\pi}(k_0f_0+k_1f_1)\,d\psi$. The inner and outer densities relative to positive arclength are $k_0/(2\pi a)$ and $k_1/(2\pi b)$. This establishes equality of the strip and annular integrals, including the certificate phase $\varphi=\pi$, with positive weights on both circles.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 34, AppendixD

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory

/-- Appendix D, PDF pp.34–35: strip weights, Fourier coefficients, periodized angular
kernels and equality of integrals against every continuous periodic boundary function.
Arclength has positive sign on both circles; phi=pi includes the certificate reference -r0. -/
theorem annularKernels (a b r phi : ℝ) (ha : 0 < a) (har : a < r) (hrb : r < b) :
    let ell := Real.log (b/a)
    let theta := Real.log (r/a)/ell
    let h0 := innerWeight theta
    let h1 := outerWeight theta
    let k0 := periodized h0 ell phi
    let k1 := periodized h1 ell phi
    0 < theta ∧ theta < 1 ∧
    Integrable h0 ∧ Integrable h1 ∧
    (∀ s, 0 ≤ h0 s ∧ 0 ≤ h1 s ∧ h0 (-s) = h0 s ∧ h1 (-s) = h1 s) ∧
    (∫ s : ℝ, h0 s) = 1-theta ∧ (∫ s : ℝ, h1 s) = theta ∧
    (∀ u : ℝ, 0 < u →
      Integrable (fun s => h0 s*Real.cos (u*s)) ∧
      Integrable (fun s => h1 s*Real.cos (u*s)) ∧
      (∫ s : ℝ, h0 s*Real.cos (u*s)) = Real.sinh ((1-theta)*u)/Real.sinh u ∧
      (∫ s : ℝ, h1 s*Real.cos (u*s)) = Real.sinh (theta*u)/Real.sinh u) ∧
    (∀ psi, Summable (fun m : ℤ => h0 ((psi-phi+2*Real.pi*m)/ell)) ∧
      Summable (fun m : ℤ => h1 ((psi-phi+2*Real.pi*m)/ell)) ∧
      k0 psi = innerFourier a b r phi psi ∧ k1 psi = outerFourier a b r phi psi ∧
      0 ≤ k0 psi ∧ 0 ≤ k1 psi ∧
      innerDensity a b r phi psi = k0 psi/(2*Real.pi*a) ∧
      outerDensity a b r phi psi = k1 psi/(2*Real.pi*b)) ∧
    TendstoUniformlyOn (periodizedPartial h0 ell phi) k0 atTop (Set.Icc 0 (2*Real.pi)) ∧
    TendstoUniformlyOn (periodizedPartial h1 ell phi) k1 atTop (Set.Icc 0 (2*Real.pi)) ∧
    Function.Periodic k0 (2*Real.pi) ∧ Function.Periodic k1 (2*Real.pi) ∧
    (∫ psi in (0:ℝ)..(2*Real.pi), k0 psi)/(2*Real.pi) = 1-theta ∧
    (∫ psi in (0:ℝ)..(2*Real.pi), k1 psi)/(2*Real.pi) = theta ∧
    (∀ f0 f1 : ℝ → ℝ, Continuous f0 → Continuous f1 →
      Function.Periodic f0 (2*Real.pi) → Function.Periodic f1 (2*Real.pi) →
      Integrable (fun s => h0 s*f0 (phi+ell*s)+h1 s*f1 (phi+ell*s)) ∧
      (∫ s : ℝ, h0 s*f0 (phi+ell*s)+h1 s*f1 (phi+ell*s)) =
        (∫ psi in (0:ℝ)..(2*Real.pi), k0 psi*f0 psi+k1 psi*f1 psi)/(2*Real.pi)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
