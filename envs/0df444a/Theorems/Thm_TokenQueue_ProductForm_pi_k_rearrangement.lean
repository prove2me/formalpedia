-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_pi_k_rearrangement
-- name    : TokenQueue.ProductForm.pi_k_rearrangement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:56.145687+00:00
-- url     : https://prove2.me/theorems/c1deeb88-1fa4-4ee7-a672-54279eef9302
-- title:
--   Proof of (13), p. 23 (corrected: k(T1,…,Tk,T) for the printed k(T1,…,Ti,T), and Tk for the printed Tj on the left) — Πk(T1,…,Tk,T,Tk+1,…,Ti) = k(T1,…,Tk,T)Πk(T1,…,Ti)∏_{j>k} k(T1,…,Tj,T)/k(T1,…,Tj)
-- statement:
--   Assume Condition 2 ($k$ is invariant under permutations of distinct tokens) and that $k$ is positive on non-empty sequences of distinct tokens. For distinct tokens $T_1,\dots,T_i,T$ and $0\le k\le i$,
--   $$\Pi_k(T_1,\dots,T_k,T,T_{k+1},\dots,T_i)=k(T_1,\dots,T_k,T)\,\Pi_k(T_1,\dots,T_i)\prod_{j=k+1}^{i}\frac{k(T_1,\dots,T_j,T)}{k(T_1,\dots,T_j)},$$
--   where $\Pi_k(T_1,\dots,T_i)=\prod_{j=1}^i k(T_1,\dots,T_j)$.
--
--   This rearrangement moves the inserted token $T$ to the end of every prefix that contains it; it is the identity behind the third equality in the verification of (13).
--
--   **Formalization Note** **Corrected.** The page writes the leading factor as $k(T_1,\dots,T_i,T)$ and the left-hand side as $\Pi_k(T_1,\dots,T_j,T,T_{k+1},\dots,T_i)$; both are wrong for $k<i$ (the next line of the page's display already uses the correct form). `KPos` makes the divisions meaningful.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 23, Appendix A, proof of (13) ('The third equality follows from Condition 2 and the fact that …')

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

/-- Proof of (13), p. 23, corrected: under Condition 2, for distinct tokens `T₁,…,T_i,T` and
`0 ≤ k ≤ i`,
`Π_k(T₁,…,T_k,T,T_{k+1},…,T_i) = k(T₁,…,T_k,T) Π_k(T₁,…,T_i) ∏_{j=k+1}^{i} k(T₁,…,T_j,T)/k(T₁,…,T_j)`. -/
theorem pi_k_rearrangement {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (h2 : Condition2 P) (hk : KPos P) (l : List T) (t : T)
    (hl : (t :: l).Nodup) (k : ℕ) (hki : k ≤ l.length) :
    piK P (l.take k ++ t :: l.drop k) =
      kfun P (l.take k ++ [t]) * piK P l *
        ∏ j ∈ Icc (k + 1) l.length, kfun P (l.take j ++ [t]) / kfun P (l.take j) := by sorry

end TokenQueue.ProductForm
