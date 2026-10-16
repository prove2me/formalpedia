-- Prove2me | Theorems.Thm_RobustSpecClust_Round_davis_kahan
-- name    : RobustSpecClust.Round.davis_kahan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:29.019551+00:00
-- url     : https://prove2.me/theorems/5c0e41c6-453d-406b-8853-828c3bfa0c34
-- title:
--   Theorem 3 (Davis–Kahan, Yu–Wang–Samworth), p. 46, case s = 1 — ∃ orthogonal Ô, ‖U − ÛÔ‖_F ≤ 2^{3/2}‖Σ̂ − Σ‖_F / g
-- statement:
--   This is the Davis–Kahan $\sin\Theta$ theorem in the Frobenius-norm form of Yu, Wang and Samworth, for the leading eigenspace.
--
--   Let $\Sigma, \hat\Sigma \in \mathbb R^{n\times n}$ be symmetric. Let $U \in \mathbb R^{n \times r}$ have orthonormal columns that are eigenvectors of $\Sigma$, $\Sigma U = U\,\mathrm{Diag}(\lambda_1,\dots,\lambda_r)$, and suppose there is an eigengap $g > 0$ below them: for every $v$ orthogonal to the columns of $U$ and every $k$,
--   $$v^\top \Sigma v \le (\lambda_k - g)\, v^\top v,$$
--   i.e. $\lambda_r(\Sigma) - \lambda_{r+1}(\Sigma) \ge g$ (in particular the $\lambda_k$ are the $r$ largest eigenvalues). Let $\hat U \in \mathbb R^{n\times r}$ consist of orthonormal top-$r$ eigenvectors of $\hat\Sigma$. Then there is an orthogonal matrix $\hat O \in \mathbb R^{r\times r}$ with
--   $$\|U - \hat U \hat O\|_F \le \frac{2^{3/2}\,\|\hat\Sigma - \Sigma\|_F}{g}.$$
--
--   In the proof of Theorem 2 this bounds the distance between the top eigenvectors of the estimated clustering matrix $\hat X$ and those of the true clustering matrix $X^0$, step (i) of (G.6).
--
--   **Formalization Note** The paper states the theorem for eigenvectors $s, \dots, r$ with gap $\min(\lambda_{s-1}-\lambda_s, \lambda_r - \lambda_{r+1})$; this item is the case $s = 1$ (where $\lambda_0 = \infty$), the only case the paper uses. Any $g$ with $0 < g \le \lambda_r - \lambda_{r+1}$ is allowed; taking $g$ equal to the gap gives (G.5). When $r = n$ the complement is $\{0\}$ and the gap hypothesis is vacuous, as $\lambda_{n+1} = -\infty$ on the page.
-- source:
--   arXiv:1912.07546v3, Appendix G, Theorem 3, p. 46, (G.5) (citing Yu, Wang, Samworth 2015, Biometrika 102(2), Theorem 2), case s = 1

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem davis_kahan {n r : ℕ} (S Sh : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S) (hSh : Shᵀ = Sh)
    (U Uh : Matrix (Fin n) (Fin r) ℝ) (lam : Fin r → ℝ) (hU : IsTopEigvecsWith S U lam)
    (g : ℝ) (hg : 0 < g)
    (hgap : ∀ v : Fin n → ℝ, Uᵀ *ᵥ v = 0 → ∀ k, v ⬝ᵥ (S *ᵥ v) ≤ (lam k - g) * (v ⬝ᵥ v))
    (hUh : IsTopEigvecs Sh Uh) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      Real.sqrt (frobSq (U - Uh * O)) ≤ 2 ^ (3 / 2 : ℝ) * Real.sqrt (frobSq (Sh - S)) / g := by sorry

end RobustSpecClust.Round
