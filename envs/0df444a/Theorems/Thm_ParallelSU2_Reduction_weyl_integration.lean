-- Prove2me | Theorems.Thm_ParallelSU2_Reduction_weyl_integration
-- name    : ParallelSU2.Reduction.weyl_integration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:28.782455+00:00
-- url     : https://prove2.me/theorems/159aee60-c197-496d-bba3-01ea9cf963bc
-- title:
--   Eq. (15) — ∫_{SU(2)} f µ(dĝ) = ∫₀^{2π} f(θ) (1/π) sin²(θ/2) dθ for class functions
-- statement:
--   Throughout, $\mu$ is the invariant probability measure on $\mathrm{SU}(2)$ (a left- and right-invariant Borel probability measure). Every $g\in\mathrm{SU}(2)$ has eigenvalues $e^{\pm i\theta/2}$ with $\theta\in[0,2\pi]$, so $\operatorname{Re}\operatorname{Tr}g/2=\cos(\theta/2)$ and a class function is a function of $\operatorname{Re}\operatorname{Tr} g/2$.
--
--   For every continuous $F:\mathbb R\to\mathbb R$,
--   $$\int_{\mathrm{SU}(2)} F\Big(\frac{\operatorname{Re}\operatorname{Tr}g}{2}\Big)\,\mu(dg)=\frac1\pi\int_0^{2\pi}F\big(\cos(\theta/2)\big)\,\sin^2\frac\theta2\,d\theta.$$
--
--   This is the Weyl integration formula for $\mathrm{SU}(2)$, the tool by which the paper reduces every character integral to a one-dimensional trigonometric integral.
--
--   **Formalization Note** $\mathrm{SU}(2)$ is `Matrix.specialUnitaryGroup (Fin 2) ℂ` with its subspace topology. The pinned Mathlib provides no topological-group, compactness or measurable-space instance on it, so `IsTopologicalGroup`, `CompactSpace`, a `MeasurableSpace` with `BorelSpace` are taken as instance hypotheses (all true for the actual SU(2)), and the Haar measure is any probability measure `dg` that is left and right invariant. Continuity of $F$ makes both integrals finite; the paper's statement is for the class functions it integrates (trigonometric polynomials).
-- source:
--   Hayashi, Parallel Treatment of Estimation of SU(2) and Phase Estimation, arXiv:quant-ph/0407053v3, p. 9, eq. (15)

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction

/-- Hayashi p. 9, eq. (15): integration of a class function of SU(2) against the invariant
probability measure. With eigenvalues `e^{±iθ/2}`, `θ ∈ [0, 2π]`, one has `Re Tr g / 2 = cos(θ/2)`,
and `µ(dĝ)` pushes forward to `(1/π) sin²(θ/2) dθ`. Stated for every continuous profile `F`. -/
theorem weyl_integration
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (F : ℝ → ℝ) (hF : Continuous F) :
    ∫ g, F (((g : Matrix (Fin 2) (Fin 2) ℂ).trace).re / 2) ∂dg =
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..(2 * Real.pi), F (Real.cos (θ / 2)) * Real.sin (θ / 2) ^ 2 := by sorry

end ParallelSU2.Reduction
