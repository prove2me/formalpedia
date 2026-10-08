-- Prove2me | Theorems.Thm_Pegasos_Analysis_wstar_norm_bound
-- name    : Pegasos.Analysis.wstar_norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:03.414986+00:00
-- url     : https://prove2.me/theorems/fda58595-8938-4b7e-a7f7-b4c84f338cf5
-- title:
--   Proof of Theorem 1 — the SVM optimum satisfies ‖w⋆‖ ≤ 1/√λ
-- statement:
--   Let $\lambda>0$ and let $(x_i,y_i)_{i\in[m]}$ be examples with $x_i\in\mathbb R^n$ and $y_i\in\{+1,-1\}$. If $w^\star$ minimises the SVM objective
--   $$f(w) = \frac\lambda2\|w\|^2 + \frac1m\sum_{i=1}^m\max\{0, 1 - y_i\langle w, x_i\rangle\}$$
--   of Eq. (1) (that is, $w^\star$ is as in Eq. (9)), then
--   $$\|w^\star\| \le \frac{1}{\sqrt\lambda}.$$
--
--   So the optimum lies in the ball onto which projected Pegasos projects, which is the last hypothesis of Lemma 1 ($u = w^\star\in B$) in the projected case.
--
--   **Formalization Note.** The minimiser is any $w^\star$ with $f(w^\star)\le f(w)$ for all $w$; no dual problem is formalized (the paper's proof goes through the dual (14)–(15), but the statement concerns only the primal minimiser).
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), pp. 11-12, proof of Theorem 1 (with Eq. (1) and (9))

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Proof of Theorem 1** (pp. 11–12): every minimiser `w⋆` of the SVM objective (1)
(Eq. (9)) satisfies `‖w⋆‖ ≤ 1/√λ`. -/
theorem wstar_norm_bound {n m : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : ∀ w, svmObj lam x y wstar ≤ svmObj lam x y w) :
    ‖wstar‖ ≤ 1 / Real.sqrt lam := by sorry

end Pegasos.Analysis
