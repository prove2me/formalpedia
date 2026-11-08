-- Prove2me | Theorems.Thm_WeilTypeCycles_periodic_closed_form_exact_iff_average_zero
-- name    : WeilTypeCycles.periodic_closed_form_exact_iff_average_zero
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T17:55:22.572666+00:00
-- url     : https://prove2.me/theorems/be4324c9-9623-4bcd-a17a-762f412b21fc
-- title:
--   Periodic de Rham exactness is equivalent to zero cell average
-- statement:
--   Let \(w\) be a smooth complex-valued differential form of positive degree on \(\mathbb R^m\), invariant under translation by every vector in \(\mathbb Z^m\). Suppose \(dw=0\). Then \(w\) has a smooth \(\mathbb Z^m\)-periodic primitive if and only if its coefficientwise average over \([0,1]^m\) is zero. The primitive is constructed explicitly by averaging the translation homotopy. Equivalently, every closed periodic form of positive degree differs from its constant average by an exact periodic form. This is the analytic exactness step for the flat-torus de Rham comparison relevant to the Weil-type missions; extending periodic forms to ambient projective forms is a separate step.
-- source:
--   Cartan homotopy for straight translations, smooth differentiation under compact Bochner integrals, and invariance of integration over a lattice fundamental cell.

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped ContDiff

theorem WeilTypeCycles.periodic_closed_form_exact_iff_average_zero {m k : ℕ}
    (w : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin (k+1)]→L[ℝ] ℂ)
    (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x (z : Fin m → ℤ),w (x+fun i => (z i : ℝ))=w x)
    (hc : ∀ x,extDeriv w x=0) :
    (∃ b : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin k]→L[ℝ] ℂ,
      ContDiff ℝ ∞ b ∧ (∀ x (z : Fin m → ℤ),b (x+fun i => (z i : ℝ))=b x) ∧ extDeriv b=w) ↔
      (∫ x in Set.Icc (0 : Fin m → ℝ) 1,w x)=0 := by sorry
