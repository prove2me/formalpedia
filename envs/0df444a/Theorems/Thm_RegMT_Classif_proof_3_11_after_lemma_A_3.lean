-- Prove2me | Theorems.Thm_RegMT_Classif_proof_3_11_after_lemma_A_3
-- name    : RegMT.Classif.proof_3_11_after_lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:30.518977+00:00
-- url     : https://prove2.me/theorems/ac7fca76-eac9-4d42-83d3-b612403c272b
-- title:
--   Proof of Theorem 3.11, p. 35 — finite program with conjugate slopes
-- statement:
--   Let $N\ge1$, $\kappa>0$, $\rho\ge0$, and let $L$ be a nonnegative convex Lipschitz loss. For a fixed linear classifier $w$, the worst-case expected loss over the label-switching Wasserstein ball equals the infimum of $\lambda\rho+N^{-1}\sum_i s_i$ subject to
--   $$L(\hat y_i\langle w,\hat x_i\rangle)\le s_i,\qquad L(-\hat y_i\langle w,\hat x_i\rangle)-\kappa\lambda\le s_i\quad(i=1,\ldots,N),$$
--   $$\left(\sup_{\theta\in\Theta}|\theta|\right)\|w\|_*\le\lambda,\qquad \Theta=\{\theta:L^*(\theta)<\infty\}.$$
--   This is the intermediate finite program displayed before the paper identifies the slope bound with $\operatorname{lip}(L)$.
--
--   **Formalization Note** The page leaves a stray $j\in[J]$ after the two constraints, inherited from part (i); there is no such index for part (ii). The statement includes $\rho=0$, when the value identity remains valid as an infimum, without asserting attainment.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 35, proof of Theorem 3.11, display after Lemma A.3

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Classif

/-- The intermediate reformulation on p. 35, after applying Lemma A.3 and
before identifying the conjugate-domain slope with the Lipschitz modulus. -/
theorem proof_3_11_after_lemma_A_3 {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {N : ℕ} (hN : 0 < N) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L)
    (hL0 : ∀ z, 0 ≤ L z) (w : V →L[ℝ] ℝ) :
    worstCaseLoss κ ρ xhat yhat L w =
      valueTheta κ ρ xhat yhat L w := by sorry

end RegMT.Classif
