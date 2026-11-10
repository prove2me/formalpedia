-- Prove2me | Theorems.Thm_ThinShellSampling_proposition_4_1
-- name    : ThinShellSampling.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:16.571851+00:00
-- url     : https://prove2.me/theorems/38d942d8-2741-4a0c-a559-d308d5f7ef92
-- title:
--   Proposition 4.1 — shifted anisotropic quadratic tilt
-- statement:
--   Let $\nu$ be an isotropic logconcave probability measure on $\mathbb R^n$, $M\succeq0$ and $u\in\mathbb R^n$. Put $q_u(x)=\|M^{1/2}x+u\|^2$ and $\nu_s(dx)\propto e^{-sq_u(x)}\nu(dx)$ for $s\ge0$. There is a universal constant $C$ such that for every $s\ge0$,
--
--   $$
--   \operatorname{Var}_{\nu_s}q_u\le C\Big(\operatorname{tr}(M^2)+\|u\|^2\sqrt{\operatorname{tr}(M^2)+u^{\mathsf T}Mu}\Big).
--   $$
--
--   This extends Proposition 4.2 to quadratic forms that are not centered at the barycenter; with $M=\Sigma$ and $u=m$ it is the change of variables that proves Theorem 1.4.
--
--   Differences from the source:
--
--   - encoding: isotropic logconcave probability measure (full-dimensional, logconcave density) → the published `FunctionalInequalities.KLS.LogConcave` (Prékopa–Leindler on compact sets) together with the published `FunctionalInequalities.KLS.Isotropic`; reason: an isotropic measure has identity covariance, hence is full-dimensional, and a full-dimensional Prékopa–Leindler-logconcave measure has a logconcave density; the class is the same
--   - encoding: ≲ → a universal constant C > 0, chosen before n, ν, M, u, s; reason: the paper's convention (§1.3, p.12): a ≲ b means a ≤ cb for a universal c
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Proposition 4.1, p.24 (PDF p.26); proof pp.28–29 (PDF pp.30–31)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 4.1 (Shifted anisotropic quadratic tilt).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Proposition 4.1, p.24 (PDF p.26): "Let `ν` be an isotropic logconcave probability measure
on `ℝⁿ`, `M ⪰ 0`, and `u ∈ ℝⁿ`. Set `q_u(x) = ‖M^{1/2}x + u‖²` and define the probability measure
`ν_s(dx) ∝ e^{−s q_u(x)} ν(dx)` for `s ≥ 0`. Then, for every `s ≥ 0`,
`Var_{ν_s} q_u ≲ tr(M²) + ‖u‖² √(tr(M²) + uᵀMu)`."

**Formalization Note.** `≲` is a universal constant `C`, chosen before `n, ν, M, u, s`. `evariance`
(in `[0, ∞]`); `M^{1/2}` is `msqrt M`. -/
theorem proposition_4_1 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave ν → FunctionalInequalities.KLS.Isotropic ν →
      ∀ (M : Matrix (Fin n) (Fin n) ℝ), M.PosSemidef → ∀ (u : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      0 ≤ s →
      evariance (fun x => ‖Matrix.toEuclideanLin (msqrt M) x + u‖ ^ 2)
          (expTilt (ν : Measure (EuclideanSpace ℝ (Fin n)))
            (fun x => s * ‖Matrix.toEuclideanLin (msqrt M) x + u‖ ^ 2)) ≤
        ENNReal.ofReal (C * ((M * M).trace + ‖u‖ ^ 2 *
          Real.sqrt ((M * M).trace + inner ℝ u (Matrix.toEuclideanLin M u)))) := by sorry

end ThinShellSampling
