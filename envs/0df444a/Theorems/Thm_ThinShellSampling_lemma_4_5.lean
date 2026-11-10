-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_4_5
-- name    : ThinShellSampling.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:35.814807+00:00
-- url     : https://prove2.me/theorems/c5a1e7f1-6e8d-425a-bf9f-8d7062cd4a98
-- title:
--   Lemma 4.5 — properties of $M_s$ and $y_s$ along a quadratic tilt
-- statement:
--   Let $\nu$ be an isotropic logconcave probability measure on $\mathbb R^n$, $M\succ0$, and for $s\ge0$ let $\nu_s(dx)\propto e^{-s\langle x,Mx\rangle}\nu(dx)$, with barycenter $b_s$ and covariance $B_s$. Put
--
--   $$
--   y_s=M^{1/2}b_s,\qquad M_s=M^{1/2}B_sM^{1/2},
--   $$
--
--   let $\lambda_1(r),\dots,\lambda_n(r)$ be any labeling of the eigenvalues of $M_r$ that is differentiable in $r\in[0,s]$ (one exists by Kato's perturbation theory), and define the total spectral loss and gain
--
--   $$
--   N_s=\sum_{\lambda_i(s)<\lambda_i(0)}\big(\lambda_i(0)-\lambda_i(s)\big),\qquad P_s=\sum_{\lambda_i(s)>\lambda_i(0)}\big(\lambda_i(s)-\lambda_i(0)\big).
--   $$
--
--   Then for every $s\ge0$:
--
--   1. $P_s+\|y_s\|^2\le N_s\le16s\cdot\operatorname{tr}(M_0^2)$;
--   2. $\operatorname{tr}(M_s^2)\le17\operatorname{tr}(M_0^2)$;
--   3. $y_s^{\mathsf T}M_sy_s\le8\operatorname{tr}(M_0^2)$.
--
--   Here $M_0=M$ by isotropy. The lemma controls the eigenvalues of the tilted covariance collectively, not one by one, which is what yields the dimension-free constant 336 in Proposition 4.2.
--
--   **Formalization Note** The bounds are asserted for every labeling $(\lambda_i(r))_{i}$ of the eigenvalues of $M_r$ (a permutation of the eigenvalue list of $M_r$ for each $r\in[0,s]$) whose coordinates are differentiable on $[0,s]$; the paper uses one such labeling, supplied by Kato's theorem.
--
--   Differences from the source:
--
--   - generalization: N_s, P_s computed with the differentiable labeling of the eigenvalues of M_s that Kato's theorem provides (proof of Lemma 4.4, p.26) → the bounds hold for every labeling of the eigenvalues of M_r whose coordinates are differentiable on [0, s]; reason: the paper's labeling is one such labeling, so the Lean statement specializes to the paper's; the proof (Cauchy–Schwarz in time with ∂λ_i = u_iᵀ(∂M_s)u_i) applies to any differentiable labeling
--   - reading: M ≻ 0 stated only in the surrounding text → hypothesis M.PosDef; reason: standing hypothesis of §4.1, p.25: "We first prove the proposition for M ≻ 0"
--   - encoding: isotropic logconcave probability measure (full-dimensional, logconcave density) → the published `FunctionalInequalities.KLS.LogConcave` (Prékopa–Leindler on compact sets) together with the published `FunctionalInequalities.KLS.Isotropic`; reason: an isotropic measure has identity covariance, hence is full-dimensional, and a full-dimensional Prékopa–Leindler-logconcave measure has a logconcave density; the class is the same
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 4.5, p.27 (PDF p.29); setting §4.1, pp.25–27 (PDF pp.27–29)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_covMat

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Lemma 4.5 (Properties of `M_s` and `y_s`).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Lemma 4.5, p.27 (PDF p.29), in the setting of §4.1, pp.25–27 (PDF pp.27–29): `ν` is an
isotropic logconcave probability measure on `ℝⁿ`, `M ≻ 0`, `ν_s ∝ exp(−s xᵀMx) ν`, `b_s = E_s X`,
`B_s = cov_s X`, and
`N_s := Σ_{λ_i(s)<λ_i(0)} (λ_i(0) − λ_i(s))`, `P_s := Σ_{λ_i(s)>λ_i(0)} (λ_i(s) − λ_i(0))`,
where (proof of Lemma 4.4, p.26) "the eigenvalues `λ_i(s)` of `M_s` may be labeled differentiably".
"The barycenter `y_s = M^{1/2} b_s` and covariance `M_s = M^{1/2} B_s M^{1/2}` satisfy the following
bounds for `s ≥ 0`: `P_s + ‖y_s‖² ≤ N_s ≤ 16s · tr(M_0²)`; `tr(M_s²) ≤ 17 tr(M_0²)`;
`y_sᵀ M_s y_s ≤ 8 tr(M_0²)`."

**Formalization Note.**
* The labeling `λ_i(r)` is **any** labeling of the eigenvalues of `M_r` (for each `r ∈ [0, s]`,
  `(λ_i(r))_i` is a permutation of the eigenvalue list of `M_r`) such that each `r ↦ λ_i(r)` is
  differentiable on `[0, s]`; such a labeling exists by Kato's perturbation theorem [Kat95, Thm 6.8],
  which is what the paper invokes. `N_s` and `P_s` are computed with that labeling.
* Logconcavity is the published compact-set Prékopa–Leindler definition
  `FunctionalInequalities.KLS.LogConcave` and isotropy the published
  `FunctionalInequalities.KLS.Isotropic`; together they mean "isotropic logconcave".
* `M_0 = M^{1/2} cov(ν) M^{1/2}` (equal to `M` by isotropy) is written as in the paper. -/
theorem lemma_4_5 (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave ν) (hiso : FunctionalInequalities.KLS.Isotropic ν)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (s : ℝ) (hs : 0 ≤ s) :
    let νs : ℝ → Measure (EuclideanSpace ℝ (Fin n)) := fun r =>
      expTilt (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (fun x => r * inner ℝ x (Matrix.toEuclideanLin M x))
    let Ms : ℝ → Matrix (Fin n) (Fin n) ℝ := fun r => msqrt M * covMat (νs r) * msqrt M
    let ys : EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin (msqrt M) (mean (νs s))
    ∀ lam : ℝ → Fin n → ℝ,
      (∀ r ∈ Set.Icc 0 s, ∃ σ : Equiv.Perm (Fin n), lam r = sortedEig (Ms r) ∘ σ) →
      (∀ i, DifferentiableOn ℝ (fun r => lam r i) (Set.Icc 0 s)) →
      let Ns : ℝ := ∑ i, max (lam 0 i - lam s i) 0
      let Ps : ℝ := ∑ i, max (lam s i - lam 0 i) 0
      (Ps + ‖ys‖ ^ 2 ≤ Ns ∧ Ns ≤ 16 * s * (Ms 0 * Ms 0).trace) ∧
      (Ms s * Ms s).trace ≤ 17 * (Ms 0 * Ms 0).trace ∧
      inner ℝ ys (Matrix.toEuclideanLin (Ms s) ys) ≤ 8 * (Ms 0 * Ms 0).trace := by sorry

end ThinShellSampling
