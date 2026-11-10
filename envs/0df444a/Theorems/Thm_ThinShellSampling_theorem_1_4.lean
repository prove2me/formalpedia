-- Prove2me | Theorems.Thm_ThinShellSampling_theorem_1_4
-- name    : ThinShellSampling.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:20.078717+00:00
-- url     : https://prove2.me/theorems/533bfa7b-cf62-4099-a7f4-59d8fc0cae4c
-- title:
--   Theorem 1.4 — thin-shell stability along Gaussian tilts
-- statement:
--   Let $\pi$ be a logconcave probability measure on $\mathbb R^n$ with barycenter $m$, covariance $\Sigma$, $\Lambda=\|\Sigma\|_{\mathrm{op}}$, $L=\|\mathbb E_\pi[XX^{\mathsf T}]\|_{\mathrm{op}}$ and $R^2=\mathbb E_\pi\|X\|^2$, and let $\pi_t(dx)\propto e^{-\|x\|^2/(2t)}\pi(dx)$. Put $A=\operatorname{tr}(\Sigma^2)+\|m\|^2\sqrt{\operatorname{tr}(\Sigma^2)+m^{\mathsf T}\Sigma m}$. There is a universal constant $C$ such that
--
--   $$
--   \sup_{t>0}\operatorname{Var}_{\pi_t}(\|X\|^2)\le C\,A\qquad\text{and}\qquad A\le C\,\min\{R^2L,\;R^3\Lambda^{1/2}\}.
--   $$
--
--   For isotropic $\pi$ this gives $\operatorname{Var}_{\pi_t}(\|X\|^2)\lesssim n$ for all $t$, extending the thin-shell theorem to every Gaussian tilt. It is the estimate that permits annealing steps $\sigma^2\mapsto\sigma^2(1+\sigma^2/\sqrt{q\mathcal V})$ in Gaussian cooling.
--
--   **Formalization Note** Variances are in $[0,\infty]$.
--
--   Differences from the source:
--
--   - generalization: a logconcave probability measure (full-dimensional, §1.3) → the published FunctionalInequalities.KLS.LogConcave, which also admits logconcave measures supported on a proper affine subspace; reason: every full-dimensional logconcave measure is included; footnote 5, p.12: otherwise one works on the supporting affine subspace
--   - reading: sup Var ≲ A = O(R²L ∧ R³Λ^{1/2}) → ∃ universal C: sup Var ≤ C·A and A ≤ C·min(R²L, R³√Λ); reason: both relations of the display, with one universal constant (the proof gives A ≤ 2 min{…})
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.4, p.4 (PDF p.6); proof p.29 (PDF p.31)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.4 (Thin-shell stability).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.4, p.4 (PDF p.6): "Let `π` be any logconcave probability measure in `ℝⁿ`. Then,
`sup_{t>0} Var_{π_t}(‖X‖²) ≲ tr(Σ²) + ‖m‖² √(tr(Σ²) + mᵀΣm) = O(R²L ∧ R³Λ^{1/2})`."
Notation (§1.1, p.4): `π_t(dx) ∝ exp{−‖x‖²/(2t)} π(dx)`, `m = E_π X`, `Σ = cov π`, `Λ = ‖Σ‖_op`,
`L = ‖E_π[XXᵀ]‖_op`, `R² = E_π‖X‖²`.

**Formalization Note.** Both relations are stated, with one universal constant `C` chosen before
`n` and `π`: `sup_{t>0} Var ≤ C·A` and `A ≤ C·min(R²L, R³√Λ)` for
`A = tr(Σ²) + ‖m‖²√(tr(Σ²) + mᵀΣm)`. Logconcavity is the published
`FunctionalInequalities.KLS.LogConcave`, which also admits logconcave measures supported on a proper
affine subspace (the paper assumes full-dimensionality and remarks, footnote 5, p.12, that otherwise
one works on the supporting affine subspace). Variances are `evariance` (in `[0, ∞]`). -/
theorem theorem_1_4 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave π →
      let μ : Measure (EuclideanSpace ℝ (Fin n)) := π
      let A : ℝ := (covMat μ * covMat μ).trace + ‖mean μ‖ ^ 2 *
        Real.sqrt ((covMat μ * covMat μ).trace +
          inner ℝ (mean μ) (Matrix.toEuclideanLin (covMat μ) (mean μ)))
      (⨆ t : ℝ, ⨆ (_ : 0 < t), evariance (fun x => ‖x‖ ^ 2) (gaussTilt μ t)) ≤
          ENNReal.ofReal (C * A) ∧
        A ≤ C * min (rsq μ * Lmom μ) (Real.sqrt (rsq μ) ^ 3 * Real.sqrt (Lam μ)) := by sorry

end ThinShellSampling
