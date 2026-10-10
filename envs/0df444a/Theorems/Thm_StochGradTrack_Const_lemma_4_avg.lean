-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_4_avg
-- name    : StochGradTrack.Const.lemma_4_avg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:18.570001+00:00
-- url     : https://prove2.me/theorems/2ca18624-f0fd-4a3b-b7fb-b64fb13a14a9
-- title:
--   Lemma 4, (18), p. 420 — E[‖x̄_{k+1} − x*‖² | F_k] ≤ (1 − αμ)‖x̄_k − x*‖² + (αL²/(μn))(1 + αμ)‖x_k − 1x̄_k‖² + α²σ²/n
-- statement:
--   Assume Assumptions 1–4, let $x^*$ minimize $f$, and run DSGT (4) with constant stepsize $\alpha$, $0<\alpha<\frac{2}{\mu+L}$, from a deterministic $\mathbf x_0$. Then for every $k\ge0$ the random variable $\|\bar x_{k+1}-x^*\|^2$ is integrable and, almost surely,
--   $$\mathbb E\big[\|\bar x_{k+1}-x^*\|^2\mid\mathcal F_k\big]\le(1-\alpha\mu)\|\bar x_k-x^*\|^2+\frac{\alpha L^2}{\mu n}(1+\alpha\mu)\|\mathbf x_k-\mathbf 1\bar x_k\|^2+\frac{\alpha^2\sigma^2}{n}.$$
--
--   This is the first row of the linear system (21): the optimization error of the average contracts, up to the consensus error and the averaged noise.
--
--   **Formalization Note.** $\mathcal F_k=\sigma(\boldsymbol\xi_0,\dots,\boldsymbol\xi_{k-1})$; $\|\mathbf x_k-\mathbf 1\bar x_k\|^2=\sum_i\|x_{i,k}-\bar x_k\|^2$. The page cites Assumptions 1 and 2; the recursion involves $\mathbf W$, and Assumptions 3–4 are assumed as well.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 4 with (18), p. 420

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_4_avg {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) (hαμL : α < 2 / (μ + L)) :
    ∀ k, Integrable (fun ω => ‖avg (xs (fun _ => α) W g ξ x0 (k + 1) ω) - xstar‖ ^ 2) P ∧
      P[fun ω => ‖avg (xs (fun _ => α) W g ξ x0 (k + 1) ω) - xstar‖ ^ 2 | noiseSigma ξ k]
        ≤ᵐ[P] fun ω => (1 - α * μ) * ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2
          + α * L ^ 2 / (μ * n) * (1 + α * μ) * consErr (xs (fun _ => α) W g ξ x0 k ω) + α ^ 2 * σ ^ 2 / n := by sorry

end StochGradTrack.Const
