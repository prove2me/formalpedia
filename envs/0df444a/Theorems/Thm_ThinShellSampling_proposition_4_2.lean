-- Prove2me | Theorems.Thm_ThinShellSampling_proposition_4_2
-- name    : ThinShellSampling.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:15.247226+00:00
-- url     : https://prove2.me/theorems/8f38b5d1-7182-4592-ac42-44826988339a
-- title:
--   Proposition 4.2 — centered anisotropic quadratic tilt, constant 336
-- statement:
--   Let $\nu$ be an isotropic logconcave probability measure on $\mathbb R^n$, $M\succeq0$, and $\nu_s(dx)\propto e^{-s\langle x,Mx\rangle}\nu(dx)$ for $s\ge0$. Then
--
--   $$
--   \operatorname{Var}_{\nu_s}(X^{\mathsf T}MX)\le336\operatorname{tr}(M^2)\qquad\text{for every }s\ge0.
--   $$
--
--   At $s=0$ this is the anisotropic thin-shell bound (1.1); the proposition says the bound survives every quadratic tilt with a universal constant, independent of $n$ and $s$.
--
--   **Formalization Note** The variance is in $[0,\infty]$ (Mathlib's `evariance`, infinite off $L^2$).
--
--   Differences from the source:
--
--   - encoding: isotropic logconcave probability measure (full-dimensional, logconcave density) → the published `FunctionalInequalities.KLS.LogConcave` (Prékopa–Leindler on compact sets) together with the published `FunctionalInequalities.KLS.Isotropic`; reason: an isotropic measure has identity covariance, hence is full-dimensional, and a full-dimensional Prékopa–Leindler-logconcave measure has a logconcave density; the class is the same
--   - encoding: Var_{ν_s} → Mathlib evariance in [0, ∞]; reason: equals the variance on L² and ∞ otherwise; a real variance would be 0 off L²
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Proposition 4.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_ThinShellSampling_expTilt

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 4.2 (Centered anisotropic quadratic tilt).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Proposition 4.2, p.25 (PDF p.27): "Let `ν` be an isotropic logconcave probability measure
on `ℝⁿ`, and `ν_s(dx) ∝ e^{−s⟨x,Mx⟩} ν(dx)` for `s ≥ 0` and `M ⪰ 0`. Then,
`Var_{ν_s}(XᵀMX) ≤ 336 tr(M²)` for every `s ≥ 0`."

**Formalization Note.** The variance is Mathlib's `evariance` (in `[0, ∞]`, infinite off `L²`), so
the bound is not made vacuous by a junk value. Isotropic logconcave = the published
`FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`. -/
theorem proposition_4_2 (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave ν) (hiso : FunctionalInequalities.KLS.Isotropic ν)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    evariance (fun x => inner ℝ x (Matrix.toEuclideanLin M x))
        (expTilt (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (fun x => s * inner ℝ x (Matrix.toEuclideanLin M x))) ≤
      ENNReal.ofReal (336 * (M * M).trace) := by sorry

end ThinShellSampling
