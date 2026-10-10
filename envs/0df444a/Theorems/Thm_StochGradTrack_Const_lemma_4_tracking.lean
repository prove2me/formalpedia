-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_4_tracking
-- name    : StochGradTrack.Const.lemma_4_tracking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:13.5644+00:00
-- url     : https://prove2.me/theorems/5f822621-c8f3-4ecd-a925-5ee0af0ab353
-- title:
--   Lemma 4, (20), p. 420 — the conditional tracking-error recursion for E[‖y_{k+1} − 1ȳ_{k+1}‖² | F_k], for any β > 0 (with 3αL ≤ 1)
-- statement:
--   Assume Assumptions 1–4, let $x^*$ minimize $f$, and run DSGT (4) with constant stepsize $\alpha$, where $0<\alpha<\frac{2}{\mu+L}$ and $3\alpha L\le1$. Let $\rho=\rho_w$, $w=\|\mathbf W-\mathbf I\|$ (Frobenius) and $M_\sigma=[3\alpha^2L^2+2(\alpha L+1)(n+1)]\sigma^2$. Then for every $\beta>0$ and every $k\ge0$, $\|\mathbf y_{k+1}-\mathbf 1\bar y_{k+1}\|^2$ is integrable and, almost surely,
--   $$\begin{aligned}\mathbb E\big[\|\mathbf y_{k+1}-\mathbf 1\bar y_{k+1}\|^2\mid\mathcal F_k\big]\le{}&(1+4\alpha L+2\alpha^2L^2+\beta)\rho^2\,\mathbb E\big[\|\mathbf y_k-\mathbf 1\bar y_k\|^2\mid\mathcal F_k\big]\\&+\Big(\frac1\beta w^2L^2+2w^2L^2+3\alpha L^3\Big)\|\mathbf x_k-\mathbf 1\bar x_k\|^2+2\alpha nL^3\|\bar x_k-x^*\|^2+M_\sigma .\end{aligned}$$
--
--   This is the third row of the linear system (21), coupling the tracking error to the consensus and optimization errors.
--
--   **Formalization Note.** The hypothesis $3\alpha L\le1$ is not on the page. The last step of the proof, (76) on p. 445, replaces $3\alpha^2nL^4+\alpha nL^3$ by $2\alpha nL^3$ and $2\alpha L^3+3\alpha^2L^4$ by $3\alpha L^3$, which needs $3\alpha L\le1$; "$\alpha<2/(\mu+L)$" does not imply it. The hypothesis is added so that the statement is the one the proof establishes. The page cites Assumptions 1–2; Assumptions 3–4 are assumed as well.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 4 with (20), p. 420; proof in App. 7.1, (76), p. 445

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_4_tracking {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) (hαμL : α < 2 / (μ + L))
    (hαL : 3 * α * L ≤ 1) (β : ℝ) (hβ : 0 < β) :
    ∀ k, Integrable (fun ω => consErr (ys (fun _ => α) W g ξ x0 (k + 1) ω)) P ∧
      P[fun ω => consErr (ys (fun _ => α) W g ξ x0 (k + 1) ω) | noiseSigma ξ k]
        ≤ᵐ[P] fun ω => (1 + 4 * α * L + 2 * α ^ 2 * L ^ 2 + β) * rhoW W ^ 2
              * (P[fun ω' => consErr (ys (fun _ => α) W g ξ x0 k ω') | noiseSigma ξ k]) ω
          + (1 / β * frobWI W ^ 2 * L ^ 2 + 2 * frobWI W ^ 2 * L ^ 2 + 3 * α * L ^ 3)
              * consErr (xs (fun _ => α) W g ξ x0 k ω)
          + 2 * α * n * L ^ 3 * ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2 + Msigma α L n σ := by sorry

end StochGradTrack.Const
