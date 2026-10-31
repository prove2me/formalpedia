-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_continuous_and_l2_paths
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.continuous_and_l2_paths
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:49:31.706962+00:00
-- url     : https://prove2.me/theorems/44304eaa-6ab5-4852-92a6-fc3b8c659289
-- title:
--   Example 8.1: continuous and L2 path-space RKHS
-- statement:
--   For a centered Gaussian process on $[0,1]$, retain the following two settings. A Borel $C[0,1]$-valued version has its coordinate covariance RKHS isometrically, and its covariance kernel is continuous. Under the canonical inclusion in $L^2[0,1]$ the same RKHS and norm are obtained. Separately, a jointly measurable process with almost surely finite $\int_0^1W_s^2\,ds$ defines a Borel Gaussian $L^2$ element $X$. Its dual is represented by $\ell_f(g)=\int fg$, its covariance satisfies
--   $$Sf(t)=\int_0^1K(s,t)f(s)\,ds\quad\text{a.e. }t,\qquad\langle Sf,Sg\rangle_H=\int_0^1\!\int_0^1K(s,t)f(s)g(t)\,ds\,dt,$$
--   and these covariance images are dense in its RKHS for the Hilbert norm. Only the $L^2$ branch identifies functions modulo time-null sets.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 18, Example 8.1: continuous and L2 path-space RKHS

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Example 8.1: continuous and L2 path-space RKHS, arXiv:0805.3252v1, PDF p.18.
The branches are separate universal clauses. Joint measurability plus a.e. MemLp exactly expresses the second branch, without assuming Gaussian norm moments. Kernel equality is equality of L² classes. The C-to-L² inclusion is injective for continuous paths. -/
theorem continuous_and_l2_paths :
(∀ V : Omega → C(Time, ℝ), BorelCenteredGaussianElement P V →
      (fun f : C(Time, ℝ) => fun t => f t) '' banachRKHS P V =
        processRKHS P (fun t o => V o t) ∧
      Continuous (fun st : Time × Time => processCovariance P (fun t o => V o t) st.1 st.2) ∧
      banachRKHS P (fun o => toL2 timeMeasure (V o)) =
        (fun f : C(Time, ℝ) => toL2 timeMeasure f) '' banachRKHS P V ∧
      ∀ h ∈ banachRKHS P V,
        banachNorm P (fun o => toL2 timeMeasure (V o)) (toL2 timeMeasure h) =
          banachNorm P V h) ∧
    (∀ W : Time → Omega → ℝ, CenteredProcess P W →
      Measurable (fun p : Time × Omega => W p.1 p.2) →
      (∀ᵐ o ∂P, MemLp (fun t => W t o) 2 timeMeasure) →
      let X := fun o => toL2 timeMeasure (fun t => W t o)
      let S := fun f : TimeL2 => covarianceMap P X (innerSL ℝ f)
      BorelCenteredGaussianElement P X ∧
      (∀ l : TimeL2 →L[ℝ] ℝ, ∃ f : TimeL2, l = innerSL ℝ f) ∧
      (∀ f : TimeL2, S f = toL2 timeMeasure
        (fun t => ∫ s, processCovariance P W s t * f s ∂timeMeasure)) ∧
      (∀ f g : TimeL2, banachInner P X (S f) (S g) =
        ∫ t, ∫ s, processCovariance P W s t * f s * g t ∂timeMeasure ∂timeMeasure) ∧
      (∀ f : TimeL2, S f ∈ banachRKHS P X) ∧
      ∀ h ∈ banachRKHS P X, ∀ e : ℝ, 0 < e →
        ∃ f : TimeL2, h - S f ∈ banachRKHS P X ∧ banachNorm P X (h - S f) < e) := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
