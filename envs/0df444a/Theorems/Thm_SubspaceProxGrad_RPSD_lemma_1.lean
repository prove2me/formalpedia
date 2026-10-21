-- Prove2me | Theorems.Thm_SubspaceProxGrad_RPSD_lemma_1
-- name    : SubspaceProxGrad.RPSD.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:55.410255+00:00
-- url     : https://prove2.me/theorems/017198af-7be5-4dfd-a611-079c56f91b54
-- title:
--   Lemma 1, p. 3 — for an admissible selection, P = 𝔼[P_𝔖] is positive definite with λmin(P) > 0 and λmax(P) ≤ 1
-- statement:
--   Let $n\ge1$ and let $\mathfrak S$ be a random subspace of $\mathbb R^n$ on a probability space $(\Omega,\mathcal A,\mathbb P)$, such that $\omega\mapsto P_{\mathfrak S(\omega)}x$ is measurable for each $x$. Suppose $\mathfrak S$ is admissible, i.e. $\mathbb P[x\in\mathfrak S^\perp]<1$ for every $x\neq0$, and let $\mathsf P=\mathbb E[P_{\mathfrak S}]$ be the average projection. Then $\mathsf P$ is a symmetric positive definite matrix, and its extreme eigenvalues satisfy
--   $$\lambda_{\min}(\mathsf P)>0\qquad\text{and}\qquad\lambda_{\max}(\mathsf P)\le 1 .$$
--   Precisely: $\mathsf P$ is self-adjoint, $\langle x,\mathsf Px\rangle>0$ for every $x\ne0$, and the Rayleigh extremes satisfy the two bounds above.
--
--   The average projection and its extreme eigenvalues govern the whole analysis of RPSD: $\lambda_{\min}(\mathsf P)>0$ is what makes the contraction factor of Theorem 1 strictly less than one, and positive definiteness is what makes $\mathsf Q=\mathsf P^{-1/2}$ well defined.
--
--   **Formalization Note.** The hypothesis $n\ge1$ is added: on $\mathbb R^0$ there are no eigenvalues, and the Rayleigh infimum over the empty unit sphere is $0$. "Positive definite matrix" is read as self-adjoint plus $\langle x,\mathsf Px\rangle>0$ for $x\neq0$. The measurability hypothesis guarantees that the Bochner integral defining $\mathsf P$ is the true expectation.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, p. 3, Lemma 1 (display (2))

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

theorem lemma_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (S : Ω → Submodule ℝ (E n))
    (hS : ∀ x : E n, Measurable fun ω => (S ω).starProjection x)
    (hadm : IsAdmissible pr S) (P : E n →L[ℝ] E n) (hP : IsAvgProj pr S P) :
    IsSelfAdjoint P ∧ (∀ x : E n, x ≠ 0 → 0 < inner ℝ x (P x)) ∧
      0 < lamMin P ∧ lamMax P ≤ 1 := by sorry

end SubspaceProxGrad.RPSD
