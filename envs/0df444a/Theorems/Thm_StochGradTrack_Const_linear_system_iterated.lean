-- Prove2me | Theorems.Thm_StochGradTrack_Const_linear_system_iterated
-- name    : StochGradTrack.Const.linear_system_iterated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:25.584361+00:00
-- url     : https://prove2.me/theorems/97a98153-90ec-4505-9d20-90111674300d
-- title:
--   (22), p. 421 — e_k ≤ A^k e_0 + Σ_{l<k} A^l (α²σ²/n, 0, M_σ) componentwise
-- statement:
--   Under the hypotheses of (21) and with $e_k$ and $\mathbf A$ as there, the three integrands are integrable for every $k$, and for every $k\ge0$, componentwise,
--   $$\begin{bmatrix}\mathbb E\|\bar x_k-x^*\|^2\\\mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2\\\mathbb E\|\mathbf y_k-\mathbf 1\bar y_k\|^2\end{bmatrix}\le\mathbf A^k\begin{bmatrix}\mathbb E\|\bar x_0-x^*\|^2\\\mathbb E\|\mathbf x_0-\mathbf 1\bar x_0\|^2\\\mathbb E\|\mathbf y_0-\mathbf 1\bar y_0\|^2\end{bmatrix}+\sum_{l=0}^{k-1}\mathbf A^l\begin{bmatrix}\alpha^2\sigma^2/n\\0\\M_\sigma\end{bmatrix}.$$
--
--   Once $\rho(\mathbf A)<1$, the first term vanishes geometrically and the sum converges to $(\mathbf I-\mathbf A)^{-1}B$, which yields the limiting bounds of Theorem 1.
--
--   **Formalization Note.** The hypothesis $3\alpha L\le1$ is inherited from (20). $\mathbf x_0$ is deterministic, so the first two entries of $e_0$ are numbers.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.1, (22), p. 421

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem linear_system_iterated {n p m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Stack n p)
    (hM : Model P f gradf μ L g ξ σ W xstar) (α : ℝ) (hα : 0 < α) (hαμL : α < 2 / (μ + L))
    (hαL : 3 * α * L ≤ 1) (β : ℝ) (hβ : 0 < β) :
    (∀ k, Integrable (fun ω => ‖avg (xs (fun _ => α) W g ξ x0 k ω) - xstar‖ ^ 2) P ∧
        Integrable (fun ω => consErr (xs (fun _ => α) W g ξ x0 k ω)) P ∧ Integrable (fun ω => consErr (ys (fun _ => α) W g ξ x0 k ω)) P) ∧
      ∀ k i, errVec P (fun _ => α) W g ξ x0 xstar k i
        ≤ ((Agen α β μ L n (rhoW W) (frobWI W)) ^ k *ᵥ errVec P (fun _ => α) W g ξ x0 xstar 0
            + ∑ l ∈ Finset.range k, (Agen α β μ L n (rhoW W) (frobWI W)) ^ l *ᵥ noiseVec α L n σ) i
      := by sorry

end StochGradTrack.Const
