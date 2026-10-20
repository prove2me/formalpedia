-- Prove2me | Theorems.Thm_TargetedClosure_Stability_lemma_2_1
-- name    : TargetedClosure.Stability.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:05.869643+00:00
-- url     : https://prove2.me/theorems/23664385-4873-47fc-8a74-8cc0c09ac7d9
-- title:
--   Lemma 2.1 — reproduction rate below one iff the activity LMI holds
-- statement:
--   In the spatial compartmental epidemic model, let $\mathcal R_e=\lambda_1(F(x)V^{-1})$ be the effective reproduction rate. Let $T=(\tau_{ij})$, $X=\operatorname{diag}(x_i)$, $\Lambda=\operatorname{diag}((\sum_lN_l\tau_{lk})^{-1})$, and $\widehat N=\operatorname{diag}(N_i)$. For activity levels $x_i\in[0,1]$ and the model's standing assumptions, Lemma 2.1 states
--
--   $$
--   \mathcal R_e<1\quad\Longleftrightarrow\quad
--   TX\Lambda T^{\mathsf T}\prec
--   \widehat N^{-1}\frac{(\mu+\kappa)(\mu+\gamma)}{(\rho+\alpha(1-\rho))\beta\kappa}.
--   $$
--
--   Here $A\prec B$ means that $B-A$ is positive definite. The equivalence turns the stability threshold into a linear matrix inequality in the activity levels.
--
--   **Formalization Note** The paper leaves $X$ implicit; it is the diagonal activity matrix. The formalization adds $\rho+\alpha(1-\rho)>0$ because the displayed fraction is undefined when $\rho=\alpha=0$. The spectral radius includes complex eigenvalues of the full $3n\times3n$ next generation matrix.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), p. 13 (PDF 14), Lemma 2.1; proof continued p. 14 (PDF 15)

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem lemma_2_1 {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    Re P x < 1 ↔
    (thr P • (Nhat P)⁻¹ - Tmat P * Xmat x * Lam P * (Tmat P).transpose).PosDef := by sorry

end TargetedClosure.Stability
