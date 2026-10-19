-- Prove2me | Theorems.Thm_RobustSpecClust_Round_eq_G6
-- name    : RobustSpecClust.Round.eq_G6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:28.103637+00:00
-- url     : https://prove2.me/theorems/6e3a7fb2-5888-4ffb-9173-745898e9f4fd
-- title:
--   (G.6), p. 46 — for the optimal rotation O, ‖Û − U⁰O‖²_F ≤ 8‖X̂ − X⁰‖₁/n²_min
-- statement:
--   Let $\varphi : [n]\to[r]$ be a labelling with every cluster nonempty ($r \ge 1$), $X^0$ the true clustering matrix and $U^0 = Z^0\,\mathrm{Diag}(1/\sqrt{n_k})$. Let $\hat X \in \mathbb R^{n\times n}$ be symmetric with $0 \le \hat X_{ij} \le 1$, and let $\hat U \in \mathbb R^{n \times r}$ consist of orthonormal top-$r$ eigenvectors of $\hat X$. Let $O$ be an optimal rotation, i.e. an orthogonal $r\times r$ matrix minimising $\|\hat U - U^0 O'\|_F$ over all orthogonal $O'$. Then
--   $$\|\hat U - U^0 O\|_F^2 \;\le\; \frac{8\,\|\hat X - X^0\|_1}{n_{\min}^2}.$$
--
--   This is the eigenvector-perturbation step of the proof of Theorem 2: it combines the Davis–Kahan theorem, the eigengap $n_{\min}$ of $X^0$ and the box constraint on $\hat X$.
--
--   **Formalization Note** The page writes $\|\hat U - U^0O\|_F^2$ without naming $O$; §4.2 (p. 17) calls it "the optimal rotation matrix". The statement is made for every minimiser $O$ (minimisers exist since the orthogonal group is compact), which is stronger than the existence of one good $O$.
-- source:
--   arXiv:1912.07546v3, Appendix G, proof of Theorem 2, p. 46, (G.6); O as in §4.2, p. 17 ("the optimal rotation matrix")

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem eq_G6 {n r : ℕ} [NeZero r] (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (Xh : Matrix (Fin n) (Fin n) ℝ) (hsym : Xhᵀ = Xh) (hbox : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1)
    (Uh : Matrix (Fin n) (Fin r) ℝ) (hU : IsTopEigvecs Xh Uh)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (hOopt : ∀ O' ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      frobSq (Uh - U0 φ * O) ≤ frobSq (Uh - U0 φ * O')) :
    frobSq (Uh - U0 φ * O) ≤ 8 * l1 (Xh - trueClust φ) / nmin φ ^ 2 := by sorry

end RobustSpecClust.Round
