-- Prove2me | Theorems.Thm_TargetedClosure_Stability_loewner_form
-- name    : TargetedClosure.Stability.loewner_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:08.130172+00:00
-- url     : https://prove2.me/theorems/c475fc7d-8e11-4e4a-b4fa-655a7dcc30b7
-- title:
--   Proof of Lemma 2.1 — spectral bound in Loewner form
-- statement:
--   Let $S=\widehat N^{1/2}TX\Lambda T^{\mathsf T}\widehat N^{1/2}$ and $c=(\mu+\kappa)(\mu+\gamma)/((\rho+\alpha(1-\rho))\beta\kappa)$. Under the model and activity assumptions,
--
--   $$
--   \lambda_1(S)<c\quad\Longleftrightarrow\quad
--   TX\Lambda T^{\mathsf T}\prec c\widehat N^{-1}.
--   $$
--
--   Here $A\prec B$ means that $B-A$ is positive definite. This is the last matrix equivalence in the proof of Lemma 2.1.
--
--   **Formalization Note** Nonnegative activity and mixing make $S$ positive semidefinite. Lean states the right side as positive definiteness of the matrix difference.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), p. 14 (PDF 15), end of proof of Lemma 2.1

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem loewner_form {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    lam1 (Nsqrt P * Tmat P * Xmat x * Lam P * (Tmat P).transpose * Nsqrt P) <
      ENNReal.ofReal (thr P) ↔
    (thr P • (Nhat P)⁻¹ - Tmat P * Xmat x * Lam P * (Tmat P).transpose).PosDef := by sorry

end TargetedClosure.Stability
