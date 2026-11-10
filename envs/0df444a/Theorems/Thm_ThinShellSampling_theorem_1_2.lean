-- Prove2me | Theorems.Thm_ThinShellSampling_theorem_1_2
-- name    : ThinShellSampling.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:14.901597+00:00
-- url     : https://prove2.me/theorems/a0891f7b-9a00-4775-990c-15131e6e1a3f
-- title:
--   Theorem 1.2 — hypercontractivity of the heat adjoint under (LSI)
-- statement:
--   Let $\nu$ be a probability measure on $\mathbb R^n$ satisfying (LSI) with constant $C>0$, let $\gamma_t=N(0,tI_n)$, $\nu_t=\nu*\gamma_t$, and let $Q_t$ be the heat adjoint, $Q_tf=P_t(f\nu)/P_t\nu$. For $p\in(1,\infty)$ put
--
--   $$
--   q(t)=1+(p-1)\Big(1+\frac tC\Big).
--   $$
--
--   Then for all $p\in(1,\infty)$, $t\ge0$ and $f\in L^p(\nu)$,
--
--   $$
--   \|Q_tf\|_{L^{q(t)}(\nu_t)}\le\|f\|_{L^p(\nu)}.
--   $$
--
--   Unlike Gross' hypercontractivity, the reference measure $\nu_t$ evolves with $t$. Taking $f=d\mu/d\nu$ gives $\mathsf R_{q(t)}(\mu_t\,\|\,\nu_t)\le\mathsf R_p(\mu\,\|\,\nu)$: the heat flow raises the Rényi order of a warm start, which is what keeps Rényi warmness alive through annealing.
--
--   **Formalization Note** $|\nabla f|$ in (LSI) is the local slope. Norms are $[0,\infty]$-valued `eLpNorm`.
--
--   Differences from the source:
--
--   - generalization: the log-Sobolev constant C_LSI(ν) < ∞ and q(t) = 1 + (p − 1)(1 + t/C_LSI(ν)) → every C > 0 with LSI C ν, and q(t) = 1 + (p − 1)(1 + t/C); reason: the least LSI constant is attained, so C = C_LSI(ν) > 0 gives the printed statement; the Lean form also covers C_LSI(ν) = 0, where t/C_LSI is undefined as printed
--   - encoding: |∇f| for locally Lipschitz f → the local slope limsup_{y→x} |f(y) − f(x)|/‖y − x‖ (published LocalSlope.apply); reason: equals ‖∇f(x)‖ where f is differentiable; Mathlib's fderiv would vanish at non-differentiable points of a singular ν
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.2, p.3 (PDF p.5); proof pp.21–23 (PDF pp.23–25)

import Mathlib
import Definitions.Def_ThinShellSampling_LSI
import Definitions.Def_ThinShellSampling_heatAdjoint

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.2 (Hypercontractivity under heat flow).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.2, p.3 (PDF p.5): "Let `ν` be a probability measure satisfying (LSI) with
`C_LSI(ν) < ∞`. Let `ν_t = ν ∗ γ_t` for `t ≥ 0`, and define `q : [0, ∞) → (1, ∞)` by
`(q(t) − 1)/(p − 1) = 1 + t/C_LSI(ν)` for any `p ∈ (1, ∞)`. Then, the `L²(ν)`-adjoint `Q_t` of the heat
semigroup satisfies `‖Q_t f‖_{L^{q(t)}(ν_t)} ≤ ‖f‖_{L^p(ν)}` for all `p ∈ (1, ∞)`, `t ≥ 0`, and
`f ∈ L^p(ν)`."

**Formalization Note.** Stated for every constant `C > 0` with `LSI C ν` (local-slope gradient), with
`q(t) = 1 + (p − 1)(1 + t/C)`; at `C = C_LSI(ν) > 0` (the least constant is attained) this is the
printed statement. Norms are Mathlib's `eLpNorm` (in `[0, ∞]`). -/
theorem theorem_1_2 (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (C : ℝ)
    (hC : 0 < C) (hLSI : LSI C ν) (p t : ℝ) (hp : 1 < p) (ht : 0 ≤ t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) (ν : Measure (EuclideanSpace ℝ (Fin n)))) :
    eLpNorm (heatAdjoint (ν : Measure (EuclideanSpace ℝ (Fin n))) t f)
        (ENNReal.ofReal (1 + (p - 1) * (1 + t / C)))
        ((ν : Measure (EuclideanSpace ℝ (Fin n))) ∗ gaussianT n t) ≤
      eLpNorm f (ENNReal.ofReal p) (ν : Measure (EuclideanSpace ℝ (Fin n))) := by sorry

end ThinShellSampling
