-- Prove2me | Theorems.Thm_SaddleSplit_Async_lemma_A_1
-- name    : SaddleSplit.Async.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:35.472256+00:00
-- url     : https://prove2.me/theorems/4fbcc33a-d804-4e74-acc7-9eabb5c1f822
-- title:
--   Lemma A.1, p. 30 — resolvents of a maximally monotone operator map bounded data to bounded sequences
-- statement:
--   Let $\mathcal K$ be a real Hilbert space and $A:\mathcal K\to 2^{\mathcal K}$ maximally monotone. Let $(x_n)_{n\in\mathbb N}$ be a bounded sequence in $\mathcal K$ and $(\gamma_n)_{n\in\mathbb N}$ a bounded sequence in $\left]0,+\infty\right[$. Then
--   $$\big(J_{\gamma_nA}\,x_n\big)_{n\in\mathbb N}\ \text{is bounded},$$
--   where $J_{\gamma A}=(\mathrm{Id}+\gamma A)^{-1}$ is the resolvent.
--
--   This lemma gives boundedness of the auxiliary sequences $a_n$, $b_n$, $d_n$ of Algorithm 3.4.
--
--   **Formalization Note** The resolvents are a given family of maps $J(\gamma)$ with $\gamma^{-1}(x-J(\gamma)x)\in A(J(\gamma)x)$ for every $x$ and every $\gamma>0$ (for maximally monotone $A$ such maps exist and are unique).
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 30, Lemma A.1

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Lemma A.1, p. 30: for maximally monotone `A`, a bounded sequence `(x_n)` and a bounded
sequence `(γ_n)` in `]0, +∞[`, the sequence `(J_{γ_n A} x_n)` is bounded. -/
theorem lemma_A_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E → Set E) (hA : IsMaximalMonotone A)
    (J : ℝ → E → E) (hJ : ∀ γ : ℝ, 0 < γ → IsResolvent γ A (J γ))
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x))
    (γ : ℕ → ℝ) (hγpos : ∀ n, 0 < γ n) (hγ : Bornology.IsBounded (Set.range γ)) :
    Bornology.IsBounded (Set.range fun n => J (γ n) (x n)) := by sorry

end SaddleSplit.Async
