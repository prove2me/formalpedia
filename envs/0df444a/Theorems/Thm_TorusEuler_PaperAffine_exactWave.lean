-- Prove2me | Theorems.Thm_TorusEuler_PaperAffine_exactWave
-- name    : TorusEuler.PaperAffine.exactWave
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T19:39:32.571349+00:00
-- url     : https://prove2.me/theorems/9acf3533-4a4a-4919-ac86-d38ac0e92667
-- title:
--   Lemma 2.1 — exact affine plane waves over a linear background
-- statement:
--   **Lemma 2.1 of the frozen manuscript (cc:lem:wave).** Let $J\subseteq\mathbb{R}$ be an order-connected interval on which derivatives are unique (`UniqueDiffOn`). Let $F,P:\mathbb{R}\to\mathbb{R}$ with $F$ differentiable and $P'=F$ everywhere. Let $D(t)$ be a matrix-valued function with within-$J$ derivative $D'(t)$ such that $D'+D^2$ is symmetric and $\operatorname{tr}D=0$ on $J$. Let the wave vector $k(t)$ and amplitude $a(t)$ satisfy the Craik–Criminale equations on $J$ (`WaveOn`):
--   $$k'=-D^{\mathsf T}k,\qquad a'=-Da+\frac{2k\cdot Da}{\|k\|^2}\,k.$$
--   Then:
--
--   1. **Persistence of transverse data:** if at some $t_0\in J$ the vectors $k(t_0),a(t_0)$ are nonzero and perpendicular, they remain nonzero and perpendicular for every $t\in J$;
--   2. **Exact Euler solution:** if $k(t)\cdot a(t)=0$ for all $t\in J$, then the affine wave velocity $u(t,x)=D(t)x+F(k(t)\cdot x)\,a(t)$ is divergence-free and solves the Euler equations on $J\times\mathbb{R}^3$ with pressure $-\tfrac12 x\cdot(D'+D^2)x - p_{\mathrm w}P(k\cdot x)$, where $p_{\mathrm w}=2k\cdot Da/\|k\|^2$; all time derivatives are taken within $J$.
--
--   These exact waves (Craik–Criminale) are the building blocks of the multiscale construction: each step adds one such wave over the linear background formed by the preceding scales.
--
--   **Formalization Note** The amplitude equation is stated with the pressure coefficient $p_{\mathrm w}$ already substituted. The Euler conclusion is conditional on transversality holding on all of $J$; by clause 1 this holds whenever it holds at one time. The profile assumptions used in the paper's construction (odd, $1$-periodic, $F'(0)=1$, mean-zero primitive) are not needed for this local computation and are supplied separately by Lemma 3.1.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PaperAffineStatements.lean#L27; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/02_affine.tex#L9 (cc:lem:wave, cc:eq:wave-ode).

import Mathlib
import Definitions.Def_TorusEuler_Statement
import Definitions.Def_TorusEuler_Affine

open Set
open scoped InnerProductSpace

namespace TorusEuler.PaperAffine

/-- Lemma 2.1, `cc:lem:wave`. The Euler equations and preservation
of nonzero transverse data hold for the same affine-wave solution. -/
theorem exactWave {J : Set ℝ} (hJ : J.OrdConnected) (hDiff : UniqueDiffOn ℝ J)
    {F P : ℝ → ℝ} (hF : Differentiable ℝ F) (hP : ∀ z, HasDerivAt P (F z) z)
    {D D' : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (hD : ∀ t ∈ J, HasDerivWithinAt D (D' t) J t)
    (hS : ∀ t ∈ J, IsSelfAdjoint (D' t + (D t).comp (D t)))
    (htr : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (D t).toLinearMap = 0)
    (hWave : WaveOn J D k a) :
    (∀ ⦃t₀ : ℝ⦄, t₀ ∈ J → k t₀ ≠ 0 → a t₀ ≠ 0 → ⟪k t₀, a t₀⟫_ℝ = 0 →
      ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) ∧
    ((∀ t ∈ J, ⟪k t, a t⟫_ℝ = 0) → ∀ t ∈ J, ∀ x,
      derivWithin (fun r => affineWaveVelocity F D k a r x) J t +
        fderiv ℝ (affineWaveVelocity F D k a t) x (affineWaveVelocity F D k a t x) +
        gradient (affineWavePressure P (D' t + (D t).comp (D t))
          (affineWavePressureCoeff (D t) (k t) (a t)) (k t)) x = 0 ∧
      divergence (affineWaveVelocity F D k a t) x = 0) := by sorry

end TorusEuler.PaperAffine
