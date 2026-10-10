-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_8
-- name    : StochGradTrack.Const.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:18.340286+00:00
-- url     : https://prove2.me/theorems/c793f007-662b-4fcb-b861-3f8743b85a92
-- title:
--   Lemma 8, p. 441 — E[⟨∇_{k+1}, −G_k + ∇_k⟩ | F_k] ≤ αLnσ²
-- statement:
--   Assume Assumptions 1–4, let $x^*$ minimize $f$, and run DSGT (4) with constant stepsize $\alpha>0$ from a deterministic $\mathbf x_0$. Write $G_k=G(\mathbf x_k,\boldsymbol\xi_k)$ (rows $g_i(x_{i,k},\xi_{i,k})$) and $\nabla_k=\nabla F(\mathbf x_k)$ (rows $\nabla f_i(x_{i,k})$). Then for every $k\ge0$ the Frobenius inner product $\langle\nabla_{k+1},-G_k+\nabla_k\rangle$ is integrable and, almost surely,
--   $$\mathbb E\big[\langle\nabla_{k+1},-G_k+\nabla_k\rangle\mid\mathcal F_k\big]\le\alpha Ln\sigma^2 .$$
--
--   The next gradient $\nabla_{k+1}$ depends on the current noise only through one stepsize-weighted term, so its correlation with the current gradient error is of order $\alpha$; Lemma 8 is used in the proof of (20).
--
--   **Formalization Note.** $\langle\mathbf a,\mathbf b\rangle=\sum_i\langle a_i,b_i\rangle$; $\mathcal F_k=\sigma(\boldsymbol\xi_0,\dots,\boldsymbol\xi_{k-1})$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), App. 7.1, Lemma 8, p. 441 (notation G_k, ∇_k on p. 440)

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_8 {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) :
    ∀ k, Integrable (fun ω => frobInner (fun i => gradf i (xs (fun _ => α) W g ξ x0 (k + 1) ω i))
        (fun i => gradf i (xs (fun _ => α) W g ξ x0 k ω i) - g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω))) P ∧
      P[fun ω => frobInner (fun i => gradf i (xs (fun _ => α) W g ξ x0 (k + 1) ω i))
          (fun i => gradf i (xs (fun _ => α) W g ξ x0 k ω i) - g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω)) | noiseSigma ξ k]
        ≤ᵐ[P] fun _ => α * L * n * σ ^ 2 := by sorry

end StochGradTrack.Const
