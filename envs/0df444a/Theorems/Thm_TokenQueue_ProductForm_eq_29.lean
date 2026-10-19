-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_eq_29
-- name    : TokenQueue.ProductForm.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:46.366052+00:00
-- url     : https://prove2.me/theorems/def79821-4755-419c-a12f-b1c6d2c89c70
-- title:
--   Eq. (29), p. 24 — with n0 = 0 and k(∅) = 0, Σ_k (1 − r_k) ∏_{j>k} r_j^{nj+1} Σ_{n≤nk} r_k^n = 1 for r_j = k(T1,…,Tj)/k(T1,…,Tj,T)
-- statement:
--   Let $k$ be positive on non-empty sequences of distinct tokens, with $k(\emptyset)=0$. For distinct tokens $T_1,\dots,T_i,T$ and counts $n_1,\dots,n_i\in\mathbb N$, with $n_0=0$,
--   $$\sum_{k=0}^{i}\frac{k(T_1,\dots,T_k,T)-k(T_1,\dots,T_k)}{k(T_1,\dots,T_k,T)}\prod_{j=k+1}^{i}\left(\frac{k(T_1,\dots,T_j)}{k(T_1,\dots,T_j,T)}\right)^{n_j+1}\sum_{n=0}^{n_k}\left(\frac{k(T_1,\dots,T_k)}{k(T_1,\dots,T_k,T)}\right)^{n}=1.$$
--
--   The sum telescopes; it is the step of Appendix A that shows that the release terms of (13) add up to $\lambda_T(\{T_1,\dots,T_i\})\pi(x)$, and it is used again, with $i=j-1$ and $T=T_j$, for (14).
--
--   **Formalization Note** The page writes $k(T_1,\dots,T_kT)$ in the first numerator, a typo for $k(T_1,\dots,T_k,T)$. Neither Condition 1 nor Condition 2 is needed. The counts are an arbitrary function $n:\mathbb N\to\mathbb N$ with $n(0)=0$; prefixes are `l.take k`.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 24, Appendix A, Eq. (29)

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Eq. (29), p. 24: with `n₀ = 0` and `k(∅) = 0`, for distinct tokens `T₁,…,T_i,T` and any counts
`n₁,…,n_i`,
`∑_{k=0}^{i} (k(T₁..T_k,T) − k(T₁..T_k))/k(T₁..T_k,T) · ∏_{j=k+1}^{i} (k(T₁..T_j)/k(T₁..T_j,T))^{n_j+1}
  · ∑_{n=0}^{n_k} (k(T₁..T_k)/k(T₁..T_k,T))^n = 1`. -/
theorem eq_29 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hk : KPos P) (l : List T) (t : T) (hl : (t :: l).Nodup)
    (n : ℕ → ℕ) (hn : n 0 = 0) :
    ∑ k ∈ range (l.length + 1),
      (kfun P (l.take k ++ [t]) - kfun P (l.take k)) / kfun P (l.take k ++ [t]) *
        (∏ j ∈ Icc (k + 1) l.length, (kfun P (l.take j) / kfun P (l.take j ++ [t])) ^ (n j + 1)) *
        ∑ m ∈ range (n k + 1), (kfun P (l.take k) / kfun P (l.take k ++ [t])) ^ m = 1 := by sorry

end TokenQueue.ProductForm
