-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_mixed_samples_pure_anchor
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.mixed_samples_pure_anchor
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:00:58.875962+00:00
-- url     : https://prove2.me/theorems/9b24b491-98ce-4c58-b113-6b1b8bb0ac16
-- title:
--   Appendix G1: mixed samples with one pure anchor
-- statement:
--   Let a finite nonempty family of density operators $\rho_k$ generate all operators on the span of their supports, and assume the fixed anchor is exactly $\rho_a=|\phi\rangle\langle\phi|$. Independently choose $k$ uniformly and $t$ uniformly on $[0,1]$, and use $W(k,t)=T(k,t)HT(a,\pi)$ with $T(k,t)$ the controlled $e^{-it\rho_k}$. Define $\mathcal W$ by the actual partial trace and entrywise integral. The integrands are continuous and integrable on the interval and every finite-history unit cube. Then
--
--   $$\mathcal W(|\phi\rangle\langle\phi|)=|\phi\rangle\langle\phi|,\qquad\lim_{T\to\infty}\|\mathcal W^T(\rho)-|\phi\rangle\langle\phi|\|_1=0.$$
--
--   The anchor is the unique supported fixed density operator. Using exact output records $U\rho_kU^\dagger$ and the corresponding reverse history, the integral-defined emulator converges uniformly on supported density operators to $U\rho U^\dagger$. This is the exactly pure-anchor construction, without an unquantified near-purity extension.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 28, Appendix G1: mixed samples with one pure anchor

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.28, G1: the EXACTLY pure anchor is the unique supported fixed state of
the continuous uniform-time channel. Its convergence permits supported-input emulation;
continuity/integrability of the displayed body is asserted, not assumed. -/
theorem mixed_samples_pure_anchor [Nonempty K] (S : K → Matrix I I ℂ) (a : K)
    (hS : ∀ k, IsDensityMatrix (S k)) (hgen : Generates S)
    (phi : EuclideanSpace ℂ I) (hphi : IsState phi) (hanchor : S a = pureDensity phi) :
    (∀ (rho : Matrix I I ℂ) (k : K), Continuous (fun t : ℝ =>
      traceRight (densityConjugation (mixedGate S a k t) (Matrix.kronecker rho (pureDensity minusVector))))) ∧
    (∀ (rho : Matrix I I ℂ) (k : K) (i j : I), IntegrableOn (fun t : ℝ =>
      traceRight (densityConjugation (mixedGate S a k t)
        (Matrix.kronecker rho (pureDensity minusVector))) i j) (Set.Icc 0 1)) ∧
    (∀ (rho : Matrix I I ℂ) (U : Matrix.unitaryGroup I ℂ) (T : ℕ) (h : Fin T → K) (i j : I),
      IntegrableOn (fun ts : Fin T → ℝ => mixedHistoryOutput S a phi (U : Matrix I I ℂ) rho h ts i j)
        (Set.pi Set.univ (fun _ : Fin T => Set.Icc (0 : ℝ) 1))) ∧
    mixedSampleErasureChannel S a (pureDensity phi) = pureDensity phi ∧
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho → InSampleSupport S rho →
      mixedSampleErasureChannel S a rho = rho → rho = pureDensity phi) ∧
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho → InSampleSupport S rho →
      Tendsto (fun T : ℕ => traceNorm ((mixedSampleErasureChannel S a)^[T] rho - pureDensity phi)) atTop (nhds 0)) ∧
    (∀ (U : Matrix.unitaryGroup I ℂ) (eps : ℝ), 0 < eps → ∃ N : ℕ, ∀ T ≥ N,
      ∀ rho : Matrix I I ℂ, IsDensityMatrix rho → InSampleSupport S rho →
      traceDistance (mixedEmulate S a phi (U : Matrix I I ℂ) T rho) (densityConjugation (U : Matrix I I ℂ) rho) ≤ eps) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
