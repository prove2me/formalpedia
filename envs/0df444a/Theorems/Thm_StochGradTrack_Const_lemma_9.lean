-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_9
-- name    : StochGradTrack.Const.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:48.513986+00:00
-- url     : https://prove2.me/theorems/13656b27-9113-4247-b580-6db439c5757c
-- title:
--   Lemma 9, (73), p. 442 — E[⟨Wy_k − 1ȳ_k, −G_k + ∇_k⟩ | F_k] ≤ σ²
-- statement:
--   Assume Assumptions 1–4, let $x^*$ minimize $f$, and run DSGT (4) with constant stepsize $\alpha>0$ from a deterministic $\mathbf x_0$. With $G_k$ and $\nabla_k$ as in Lemma 8, for every $k\ge0$ the Frobenius inner product $\langle\mathbf W\mathbf y_k-\mathbf 1\bar y_k,-G_k+\nabla_k\rangle$ is integrable and, almost surely,
--   $$\mathbb E\big[\langle\mathbf W\mathbf y_k-\mathbf 1\bar y_k,-G_k+\nabla_k\rangle\mid\mathcal F_k\big]\le\sigma^2 .$$
--
--   Lemma 9 controls the cross term between the mixed trackers and the current gradient noise in the proof of (20).
--
--   **Formalization Note.** $\langle\mathbf a,\mathbf b\rangle=\sum_i\langle a_i,b_i\rangle$; row $i$ of $\mathbf W\mathbf y_k-\mathbf 1\bar y_k$ is $\sum_j w_{ij}y_{j,k}-\bar y_k$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), App. 7.1, Lemma 9 with (73), p. 442

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_9 {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) :
    ∀ k, Integrable (fun ω => frobInner (fun i => mix W (ys (fun _ => α) W g ξ x0 k ω) i - avg (ys (fun _ => α) W g ξ x0 k ω))
        (fun i => gradf i (xs (fun _ => α) W g ξ x0 k ω i) - g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω))) P ∧
      P[fun ω => frobInner (fun i => mix W (ys (fun _ => α) W g ξ x0 k ω) i - avg (ys (fun _ => α) W g ξ x0 k ω))
          (fun i => gradf i (xs (fun _ => α) W g ξ x0 k ω i) - g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω)) | noiseSigma ξ k]
        ≤ᵐ[P] fun _ => σ ^ 2 := by sorry

end StochGradTrack.Const
