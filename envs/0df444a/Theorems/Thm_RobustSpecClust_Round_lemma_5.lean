-- Prove2me | Theorems.Thm_RobustSpecClust_Round_lemma_5
-- name    : RobustSpecClust.Round.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:24.737987+00:00
-- url     : https://prove2.me/theorems/52a59ee9-60d5-4fd9-918f-b68e4b55e64a
-- title:
--   Lemma 5 (Lei–Rinaldo Lemma 5.3), pp. 45–46, (G.4) — Σ_k |S_k|δ²_k ≤ 4(4 + 2ε)‖V − V̂‖²_F
-- statement:
--   This is the approximate k-means bound of Lei and Rinaldo.
--
--   Let $\varphi : [n] \to [r]$ be a labelling with membership matrix $\Theta^* = \Theta(\varphi) \in \mathbb M_{n,r}$ and clusters $G_k = \{i : \varphi(i) = k\}$, let $B^* \in \mathbb R^{r\times r}$ with rows $b^*_1,\dots,b^*_r$, and put $V = \Theta^* B^*$. Let $\hat V \in \mathbb R^{n\times r}$ be arbitrary, $\epsilon > 0$, and let $(\hat\Theta, \hat B) = (\Theta(a), B)$ be a $(1+\epsilon)$-approximate solution of the k-means problem on the rows of $\hat V$:
--   $$\|\hat V - \hat\Theta\hat B\|_F^2 \le (1+\epsilon)\min_{\Theta\in\mathbb M_{n,r},\,B'\in\mathbb R^{r\times r}}\|\hat V - \Theta B'\|_F^2 .$$
--   Let $\bar V = \hat\Theta\hat B$ with rows $\bar v_i$, and let $\delta_1, \dots, \delta_r \ge 0$ satisfy $\delta_k \le \min_{l\ne k}\|b^*_l - b^*_k\|$. With $\mathcal S_k = \{i \in G_k : \|\bar v_i - v_i\| \ge \delta_k/2\}$,
--   $$\sum_{k=1}^r |\mathcal S_k|\,\delta_k^2 \;\le\; 4(4+2\epsilon)\,\|V - \hat V\|_F^2 .$$
--
--   The lemma converts a Frobenius-norm perturbation of a k-means-feasible embedding into a count of points whose estimated centre is far from their true centre; in Theorem 2 it is applied to $V = U^0 O$ and $\hat V = \hat U$.
--
--   **Formalization Note** The page's $\delta_k$ is implicitly a nonnegative scale; $\delta_k \ge 0$ is stated explicitly, since for a negative $\delta_k$ every point of $G_k$ would lie in $\mathcal S_k$ and the bound fails at $\hat V = V$. Membership matrices are encoded by assignments. The second part of the lemma (the permutation claim) is the separate item `theorem_2_permutation`.
-- source:
--   arXiv:1912.07546v3, Appendix G, Lemma 5, pp. 45–46, (G.1)–(G.4) (citing Lei, Rinaldo 2015, Annals of Statistics 43(1), Lemma 5.3), first part

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem lemma_5 {n r : ℕ} (φ : Fin n → Fin r) (Bstar : Matrix (Fin r) (Fin r) ℝ)
    (Vh : Matrix (Fin n) (Fin r) ℝ) (ε : ℝ) (hε : 0 < ε)
    (a : Fin n → Fin r) (B : Matrix (Fin r) (Fin r) ℝ) (hkm : IsApproxKMeans ε Vh a B)
    (δ : Fin r → ℝ) (hδ0 : ∀ k, 0 ≤ δ k)
    (hδ : ∀ k l, l ≠ k → δ k ≤ vecNorm (Bstar l - Bstar k)) :
    ∑ k, ((misSet (memb φ * Bstar) (memb a * B) φ δ k).card : ℝ) * δ k ^ 2
      ≤ 4 * (4 + 2 * ε) * frobSq (memb φ * Bstar - Vh) := by sorry

end RobustSpecClust.Round
