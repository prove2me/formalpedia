-- Prove2me | Theorems.Thm_RobustSpecClust_Round_theorem_2
-- name    : RobustSpecClust.Round.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:37.98862+00:00
-- url     : https://prove2.me/theorems/ea58cb50-f1f8-46ff-a491-dbf5b0d6de0d
-- title:
--   Theorem 2, pp. 16–17, (15), no outliers — spectral rounding with (1+ε)-approximate k-means: Σ_k |S_k|/n_k ≤ 64(2+ε)‖X⁰ − X̂‖₁/n²_min
-- statement:
--   This is the deterministic core of Theorem 2 (clustering error of the rounded solution) in the setting without outliers.
--
--   Let $\varphi : [n] \to [r]$ be the true labelling, with clusters $C_k$ of sizes $n_k > 0$, $n_{\min} = \min_k n_k$, true clustering matrix $X^0$ and $U^0 = Z^0\,\mathrm{Diag}(1/\sqrt{n_1},\dots,1/\sqrt{n_r})$. Let $\hat X \in \mathbb R^{n \times n}$ be any symmetric matrix with entries in $[0,1]$ (for instance the Robust-LP estimate). Spectral clustering on $\hat X$ proceeds as follows:
--
--   1. $\hat U \in \mathbb R^{n\times r}$ is any matrix of orthonormal top-$r$ eigenvectors of $\hat X$;
--   2. $(\hat\Theta, \hat B)$, with $\hat\Theta \in \mathbb M_{n,r}$ the membership matrix of an assignment $a$ and $\hat B \in \mathbb R^{r\times r}$, is a $(1+\epsilon)$-approximate solution ($\epsilon > 0$) of k-means on the rows of $\hat U$; the estimated membership matrix is $\hat Z = \hat\Theta$.
--
--   Let $O$ be the optimal rotation, an orthogonal matrix minimising $\|\hat U - U^0 O\|_F$, and let $\mathcal S_k = \{ i \in C_k : \|\bar v_i - v_i\| \ge 1/(2\sqrt{n_k})\}$, where $v_i$ and $\bar v_i$ are the rows of $V = U^0 O$ and $\bar V = \hat\Theta\hat B$: the points of $C_k$ whose estimated centre is far from their true centre. Then
--   $$\sum_{k\in[r]} \frac{|\mathcal S_k|}{n_k} \;\le\; 64(2+\epsilon)\,\frac{\|X^0 - \hat X\|_1}{n_{\min}^2}.$$
--
--   Combined with a bound on $\|X^0 - \hat X\|_1$ (Theorem 1 of the paper), this gives the misclassification rate of the full algorithm.
--
--   **Formalization Note** The printed Theorem 2 allows $m$ outliers and is stated with probability $1 - 2r/n_{\min}$ under a condition on $\bar\epsilon$ and $\Delta_{\min} \ge 8\sigma_{\max}\sqrt d$. As printed it is false for $m \ge 1$: the outlier rows of $U^0$ are zero, so $V$ is not k-means feasible and Lemma 5 does not apply; an explicit counterexample (two clusters of size $M$, one isolated outlier, $\hat X = \mathrm{blockdiag}(E_M, E_M, 1)$, $\epsilon = 2$, $M > 256$) violates (15). This item is the case $m = 0$, which the proof in Appendix G establishes. Inequality (15) is deterministic in $\|X^0 - \hat X\|_1$: the probability, the separation condition and the condition on $\bar\epsilon$ only serve to feed Theorem 1 into the permutation claim (item `theorem_2_permutation`), so they are omitted. The printed $n_{\min} > r$ is replaced by the weaker $n_k > 0$ for all $k$, which is all the statement needs. $\delta_k = 1/\sqrt{n_k}$ as on p. 47. The statement holds for every minimiser $O$, not just for some orthogonal matrix.
-- source:
--   arXiv:1912.07546v3, Theorem 2, pp. 16–17, (15), case m = 0 (deterministic core); proof in Appendix G, pp. 45–47; O as "the optimal rotation matrix", p. 17; δ²_k = 1/n_k, p. 47

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem theorem_2 {n r : ℕ} [NeZero r] (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (Xh : Matrix (Fin n) (Fin n) ℝ) (hsym : Xhᵀ = Xh) (hbox : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1)
    (Uh : Matrix (Fin n) (Fin r) ℝ) (hU : IsTopEigvecs Xh Uh)
    (ε : ℝ) (hε : 0 < ε) (a : Fin n → Fin r) (B : Matrix (Fin r) (Fin r) ℝ)
    (hkm : IsApproxKMeans ε Uh a B)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (hOopt : ∀ O' ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      frobSq (Uh - U0 φ * O) ≤ frobSq (Uh - U0 φ * O')) :
    ∑ k, ((misSet (U0 φ * O) (memb a * B) φ (fun k => 1 / Real.sqrt (clusterSize φ k)) k).card
        : ℝ) / clusterSize φ k
      ≤ 64 * (2 + ε) * l1 (trueClust φ - Xh) / nmin φ ^ 2 := by sorry

end RobustSpecClust.Round
