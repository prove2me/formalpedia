-- Prove2me | Theorems.Thm_PNTA_analyticAt_riemannZeta
-- name    : PNTA.analyticAt_riemannZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:04:25.392556+00:00
-- url     : https://prove2.me/theorems/9f5aa207-ad34-460d-9aef-64089dce9fb2
-- title:
--   $\zeta$ is analytic away from $s = 1$
-- statement:
--   The Riemann zeta function is analytic at every point other than its pole.
--
--   For every $s \in \mathbb{C}$ with $s \neq 1$, the function $\zeta$ is analytic at $s$.
--
--   The analytic continuation of $\zeta$ to the whole plane has a single simple pole, at $s = 1$; everywhere else it is given locally by a convergent power series. This is the hypothesis-discharging lemma that lets contour-integral arguments treat $\zeta$ as analytic on any region avoiding $s = 1$, and it is used whenever a contour is deformed inside the critical strip.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L164-L168

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Topology Filter Interval Set Asymptotics

theorem PNTA.analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by sorry
